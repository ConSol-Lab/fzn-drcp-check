#!/usr/bin/env python3
"""Benchmark Pumpkin pipelines."""

import argparse
import asyncio
import json
import os
import shutil
import sys
import tempfile
import time

from collections.abc import AsyncIterator, Iterable, Iterator
from dataclasses import asdict, dataclass
from enum import StrEnum
from itertools import product
from pathlib import Path

import numpy as np
import pandas as pd


class ProofType(StrEnum):
    SCAFFOLD, FULL = "scaffold", "full"

class Mode(StrEnum):
    BATCH, INCREMENTAL, STREAMING = "batch", "incremental", "streaming"

    @property
    def flags(self) -> list[str]:
        return [] if self is Mode.BATCH else ["-s"]

    @property
    def pipelined(self) -> bool:
        """Whether the producer and checker overlap through a FIFO."""
        return self is Mode.STREAMING

class Format(StrEnum):
    TEXT, BINARY = "text", "binary"

    @property
    def flags(self) -> list[str]:
        return ["--drcp-format", str(self)]

    @property
    def suffix(self) -> str:
        return ".bin" if self is Format.BINARY else ".drcp"

class Phase(StrEnum):
    SOLVE, PROCESS, CHECK = "solve", "process", "check"

DIMS = {"proof_type": ProofType, "mode": Mode, "format": Format}
PHASES = [str(p) for p in Phase]


TIME = shutil.which("time")
TASKSET = shutil.which("taskset")
PRLIMIT = shutil.which("prlimit")
assert TIME and TASKSET and PRLIMIT, "need GNU `time`, `taskset` and `prlimit` on PATH"

GNU_TIME_FMT = ("wall=%e user=%U sys=%S maxrss=%M majflt=%F minflt=%R "
                "fsin=%I fsout=%O waits=%w preempts=%c")


async def wait_rusage(pid: int, stat: Path) -> dict:
    _, status, _ = await asyncio.to_thread(os.wait4, pid, 0)
    f = dict(tok.split("=", 1) for tok in stat.read_text().split())
    return {"user": float(f["user"]), "sys": float(f["sys"]), "gnu_wall": float(f["wall"]),
            "peak_rss": int(f["maxrss"]) * 1024,
            "majflt": int(f["majflt"]), "minflt": int(f["minflt"]),
            "fsin": int(f["fsin"]), "fsout": int(f["fsout"]),
            "waits": int(f["waits"]), "preempts": int(f["preempts"]),
            "returncode": os.waitstatus_to_exitcode(status)}


@dataclass
class Tools:
    """The solver/processor/checker binaries."""
    solver: Path
    processor: Path
    checker: Path


@dataclass
class Stage:
    phase: Phase
    cmd: list[str | Path]
    cpu: int
    consumes: Path
    wd: Path
    max_rss: int | None   # rss cap in bytes

    @property
    def stat(self) -> Path:
        """Where GNU time writes this stage's measurement."""
        return self.wd / f"{self.phase}.stat"

    def _spawn(self) -> int:
        """Launch this stage under GNU time, on `cpu`, with `max_rss`."""
        cap = [PRLIMIT, f"--as={self.max_rss}", "--"] if self.max_rss is not None else []
        argv = [TASKSET, "-c", str(self.cpu), *cap, TIME, "-f", GNU_TIME_FMT, "-o", str(self.stat), "--", *self.cmd]
        with open(os.devnull, "wb") as null:
            return os.posix_spawn(TASKSET, [*map(str, argv)], os.environ,
                                  file_actions=[(os.POSIX_SPAWN_DUP2, null.fileno(), 1),
                                                (os.POSIX_SPAWN_DUP2, null.fileno(), 2)])


@dataclass
class StageResult:
    """A finished pipeline stage."""
    phase: Phase
    start: float
    elapsed: float
    cpu: float
    user: float # user CPU seconds
    sys: float # system/kernel CPU seconds
    gnu_wall: float # process wall per GNU time
    peak_rss: int # peak resident set, bytes
    majflt: int # major page faults
    minflt: int # minor page faults
    fsin: int # filesystem block inputs
    fsout: int # filesystem block outputs
    waits: int # voluntary context switches
    preempts: int # involuntary context switches
    returncode: int


@dataclass
class Run:
    """A finished pipeline."""
    configuration: "BenchmarkConfiguration"
    results: list[StageResult]

    @property
    def verdict(self) -> str:
        return {0: "valid", 1: "invalid"}.get(self.results[-1].returncode, "fail")

    @property
    def summary(self) -> str:
        c = self.configuration
        return f"{c.input.parent.name} {c.proof_type}/{c.mode}/{c.format} rep {c.repetition_idx} -> {self.verdict}"

    def as_json(self) -> list[dict[str, object]]:
        meta = {k: v for k, v in asdict(self.configuration).items() if k != "tools"}
        return [{**meta, **asdict(r)} for r in self.results]


@dataclass
class BenchmarkConfiguration:
    """The configuration of a single experiment."""
    tools: Tools
    input: Path
    proof_type: ProofType
    mode: Mode
    format: Format
    repetition_idx: int
    max_rss: int | None  # rss cap in bytes

    @property
    def is_proof(self) -> bool:
        """Whether `input` is a pre-generated proof."""
        return self.input.suffix in (".drcp", ".bin")

    def stages(self, wd: Path, cpu_a: int, cpu_b: int) -> tuple[list[Stage], list[Stage]]:
        """Build the pipeline."""
        flags, sflag = self.format.flags, self.mode.flags
        def stage(phase, cmd, cpu, consumes):
            return Stage(phase, cmd, cpu, consumes, wd, self.max_rss)
        if self.is_proof:
            cmd = [self.tools.checker, *sflag, *flags, self.input.with_suffix(".fzn"), self.input]
            return [stage(Phase.CHECK, cmd, cpu_a, self.input)], []
        full = (wd / "full").with_suffix(self.format.suffix)
        if self.mode.pipelined:
            full = full.with_name(full.name + ".fifo")
        check = stage(Phase.CHECK, [self.tools.checker, *sflag, *flags, self.input, full],
                      cpu_b if full.suffix == ".fifo" else cpu_a, full)
        if self.proof_type is ProofType.SCAFFOLD:
            scaffold = (wd / "scaffold").with_suffix(self.format.suffix)
            flat = [stage(Phase.SOLVE, [self.tools.solver, self.input, *flags, "--proof-path", scaffold], cpu_a, self.input),
                    stage(Phase.PROCESS, [self.tools.processor, *flags, self.input, scaffold, full], cpu_a, scaffold),
                    check]
        else:
            flat = [stage(Phase.SOLVE, [self.tools.solver, self.input, "--proof-type", "full", *flags, "--proof-path", full], cpu_a, self.input),
                    check]
        # pipelining overlaps producer and check through the FIFO
        return (flat[:-2], flat[-2:]) if self.mode.pipelined else (flat, [])

    async def run(self, cpu_a: int, cpu_b: int) -> Run:
        """Run the sequential prefix, then the concurrent group."""
        with tempfile.TemporaryDirectory(prefix="bench.") as tmp:
            prefix, overlap = self.stages(Path(tmp), cpu_a, cpu_b)
            for stage in overlap:
                if stage.consumes.suffix == ".fifo":
                    os.mkfifo(stage.consumes)
            t0 = time.monotonic()
            results = [r async for r in self.measure(self.spawn(prefix), t0)]
            results += [r async for r in self.measure(list(self.spawn(overlap)), t0)]   # list() spawns all at once
        return Run(self, results)

    def spawn(self, stages: list[Stage]) -> Iterator[tuple[Stage, int, float]]:
        for stage in stages:
            yield stage, stage._spawn(), time.monotonic()

    async def measure(self, threads: Iterable[tuple[Stage, int, float]], t0: float) -> AsyncIterator[StageResult]:
        for stage, pid, start in threads:
            m = await wait_rusage(pid, stage.stat)
            yield StageResult(stage.phase, start - t0, time.monotonic() - start, m["user"] + m["sys"], **m)


def cpu_rotation(ncpu: int) -> list[int]:
    """CPUs to use for successive runs.

    >>> cpu_rotation(8)
    [7, 5, 3, 1, 6, 4, 2, 0]
    """
    return sorted(range(ncpu), key=lambda c: (c % 2 == 0, -c))


def cpu_pairs(jobs: int, ncpu: int) -> list[tuple[int, int]]:
    """`jobs // 2` disjoint CPU pairs (one per worker), odd then even to avoid colocating hyperthreads.

    >>> cpu_pairs(8, 8)
    [(7, 5), (3, 1), (6, 4), (2, 0)]
    >>> cpu_pairs(8, 4)
    [(3, 1), (2, 0)]
    """
    rot = cpu_rotation(ncpu)
    workers = max(1, min(jobs // 2, ncpu // 2))
    return [(rot[2 * k], rot[2 * k + 1]) for k in range(workers)]


def configurations(inputs: list[Path], reps: int, types: list[ProofType], modes: list[Mode],
                   formats: list[Format], tools: Tools, max_rss: int | None) -> Iterator[BenchmarkConfiguration]:
    """Valid configurations in inputs × reps × types × modes × formats."""
    for inp, rep, pt, mode, fmt in product(inputs, range(reps), types, modes, formats):
        if inp.suffix == ".jsonl":
            continue
        if inp.suffix in (".drcp", ".bin") and (pt is not ProofType.FULL or fmt.suffix != inp.suffix
                                                or mode is Mode.STREAMING):
            continue
        yield BenchmarkConfiguration(tools, inp.resolve(), pt, mode, fmt, rep, max_rss)


async def benchmark(configs: list[BenchmarkConfiguration], jobs: int) -> list[dict[str, object]]:
    """Run `configs`."""
    queue: asyncio.Queue[BenchmarkConfiguration] = asyncio.Queue()
    for cfg in configs:
        queue.put_nowait(cfg)
    rows: list[dict[str, object]] = []
    done = 0

    async def worker(cpu_a: int, cpu_b: int) -> None:
        nonlocal done
        while not queue.empty():
            run = await queue.get_nowait().run(cpu_a, cpu_b)
            for row in run.as_json():
                print(json.dumps(row, default=str), flush=True)
                rows.append(row)
            done += 1
            print(f"[{done}/{len(configs)}] {run.summary}", file=sys.stderr, flush=True)

    await asyncio.gather(*(worker(a, b) for a, b in cpu_pairs(jobs, os.cpu_count() or 2)))
    return rows


def categorize(df: pd.DataFrame, inputs: list[str]) -> pd.DataFrame:
    """Order every categorical column by its enum's definition order."""
    for col, order in {"input": inputs, "phase": Phase, **DIMS}.items():
        df[col] = pd.Categorical(df[col], [str(v) for v in order], ordered=True)
    return df


def _boot_ci(vals) -> tuple[float, float]:
    """95% BCa-bootstrap CI for the mean."""
    from scipy.stats import bootstrap
    v = np.asarray(vals, float)
    v = v[~np.isnan(v)]
    if v.size < 2 or np.ptp(v) == 0:
        return (float(v.mean()), float(v.mean())) if v.size else (np.nan, np.nan)
    ci = bootstrap((v,), np.mean, confidence_level=0.95, n_resamples=10000, random_state=0).confidence_interval
    return (float(ci.low), float(ci.high))


def _pm(mean, lo, hi, fmt) -> str:
    """Render ``mean^{+hi}_{-lo}`` as mathtext, feeding numbers to `fmt`."""
    def t(x):
        num, unit = fmt(max(0.0, x)).split(" ")
        return rf"{num}\,\mathrm{{{unit}}}"
    return f"${t(mean)}^{{+{t(hi - mean)}}}_{{-{t(mean - lo)}}}$"


def _rss_stack(g: pd.DataFrame) -> pd.DataFrame:
    g = g.sort_values("phase")
    rss = g["peak_rss"].to_numpy(float)
    n = rss.size
    seq = n - 2 if (g["mode"].iloc[0] == "streaming" and n >= 2) else n
    ms, m = np.zeros(n), 0.0
    for i in range(seq, n):
        ms[i] = m; m += rss[i]
    return g.assign(mstart=ms)


def _label_facet(row, fm, s) -> None:
    ax = row[0]
    scen = s.groupby(["proof_type", "mode"], observed=True)["y"].mean()
    ax.set_yticks(scen.values, [m for _, m in scen.index], fontsize=7)
    tr = ax.get_yaxis_transform()
    span = s.groupby("proof_type", observed=True)["y"].agg(["min", "max", "mean"]).sort_values("max", ascending=False)
    prev = None
    for pt, r in span.iterrows():
        ax.text(-0.13, r["mean"], str(pt), transform=tr, ha="right", va="center", fontweight="bold", fontsize=8)
        if prev is not None:
            for a in row:
                a.axhline((prev + r["max"]) / 2, color="0.85", lw=.6, zorder=0)
        prev = r["min"]
    ax.text(-0.26, s["y"].mean(), fm, transform=tr, ha="center", va="center", rotation=90, fontweight="bold", fontsize=9)
    for a in row:
        a.tick_params(left=False)
    row[1].tick_params(labelleft=False)


def waterfall(df: pd.DataFrame, dest: Path) -> None:
    import matplotlib
    from matplotlib.colors import to_hex
    from matplotlib.figure import Figure
    from matplotlib.patches import Patch
    from matplotlib.ticker import EngFormatter
    matplotlib.rcParams.update({"font.family": "sans-serif", "font.sans-serif": ["Fira Sans"], "axes.axisbelow": True})
    color = dict(zip(PHASES, map(to_hex, matplotlib.color_sequences["petroff10"])))
    ES, EB = EngFormatter("s", places=1, sep=" "), EngFormatter("B", places=1, sep=" ")

    def agg(g):
        lt, ht = _boot_ci(g["elapsed"]); lm, hm = _boot_ci(g["peak_rss"])
        return pd.Series({"start": g["start"].mean(), "wall": g["elapsed"].mean(), "cpu": g["cpu"].mean(),
                          "peak_rss": g["peak_rss"].mean(), "lo_t": lt, "hi_t": ht, "lo_m": lm, "hi_m": hm})
    scen = ["format", "proof_type", "mode"]
    a = (df.groupby(scen + ["phase"], observed=True)[["start", "elapsed", "cpu", "peak_rss"]]
         .apply(agg).reset_index())
    a = pd.concat([_rss_stack(g) for _, g in a.groupby(scen, observed=True)], ignore_index=True)
    a["active"] = a["cpu"]
    fmts = list(dict.fromkeys(a["format"]))
    fig = Figure(figsize=(12, 0.24 * len(a) + 1.3))
    axs = fig.subplots(len(fmts), 2, sharex="col", sharey="row", squeeze=False)
    for r, fm in enumerate(fmts):
        s = a[a["format"] == fm].copy()
        gb = s.groupby(["proof_type", "mode"], observed=True, sort=False)
        s["y"] = -(gb.ngroup() * (len(PHASES) + 1) + gb.cumcount())
        clr = s["phase"].map(color)
        aw, am = axs[r][0], axs[r][1]
        aw.barh(s.y, s.active, left=s.start, height=1, color=clr)
        aw.barh(s.y, s.wall - s.active, left=s.start + s.active, height=1, color=clr, alpha=.3, hatch="///", ec=clr, lw=0)
        am.barh(s.y, s.peak_rss, left=s.mstart, height=1, color=clr)
        et = np.clip([s.wall - s.lo_t, s.hi_t - s.wall], 0, None)
        em = np.clip([s.peak_rss - s.lo_m, s.hi_m - s.peak_rss], 0, None)
        aw.errorbar(s.start + s.wall, s.y, xerr=et, fmt="none", ecolor="0.2", capsize=1.5, lw=.7)
        am.errorbar(s.mstart + s.peak_rss, s.y, xerr=em, fmt="none", ecolor="0.2", capsize=1.5, lw=.7)
        for b in s.itertuples():
            aw.text(b.start + b.hi_t, b.y, f"  {b.phase}: {_pm(b.wall, b.lo_t, b.hi_t, ES)}", va="center", fontsize=6)
            am.text(b.mstart + b.hi_m, b.y, f"  {_pm(b.peak_rss, b.lo_m, b.hi_m, EB)}", va="center", fontsize=6)
        _label_facet(axs[r], fm, s)
    for ax, unit in zip(axs.ravel(), ["s", "B"] * len(fmts)):
        ax.xaxis.set_major_formatter(EngFormatter(unit, sep="")); ax.tick_params(axis="x", labelsize=7)
    axs[0][0].set_title("wall-clock", fontsize=9); axs[0][1].set_title("peak RSS", fontsize=9)
    axs[0][0].set_xlim(0, (a.start + a.hi_t).max() * 1.5)
    axs[0][1].set_xlim(0, (a.mstart + a.hi_m).max() * 1.45)
    fig.legend(handles=[Patch(color=color[p], label=p) for p in PHASES] +
               [Patch(facecolor="0.7", hatch="///", ec="0.4", label="waiting (wall − CPU)")],
               ncol=4, loc="upper center", fontsize=7, frameon=False,
               title=r"bars = mean   ·   error bar and $x^{+hi}_{-lo}$ = 95% bootstrap CI", title_fontsize=7)
    fig.subplots_adjust(left=0.16, top=0.92, wspace=0.05)
    fig.savefig(dest, bbox_inches="tight")
    print(f"→ {dest}", file=sys.stderr, flush=True)


def parse_args(argv=None) -> argparse.Namespace:
    ap = argparse.ArgumentParser(description="Benchmark and plot the Pumpkin -> verified-checker pipeline.")
    ap.add_argument("-n", "--repetitions", type=int, default=5, help="repetitions per query (default: 5)")
    ap.add_argument("-j", "--jobs", type=int, default=2, help="concurrency level (default: 2; >= 2 for streaming)")
    ap.add_argument("--max-rss", type=lambda s: int(s) << 20, default=None,
                    help="per-process memory cap in MiB (an address-space limit via prlimit --as)")

    def _input(s: str) -> Path:
        assert (p := Path(s)).suffix in (".fzn", ".drcp", ".bin", ".jsonl"), \
            f"{p}: expected .fzn (solve+check), .drcp/.bin (check), or .jsonl (plot only)"
        return p
    ap.add_argument("input", type=_input, nargs="+", help=".fzn, .drcp, .bin, or .jsonl")

    def _executable(s: str) -> Path:
        assert os.access(p := Path(s), os.X_OK), f"{p}: not executable"
        return p
    ap.add_argument("--solver", type=_executable, help="pumpkin-solver binary")
    ap.add_argument("--processor", type=_executable, help="pumpkin-proof-processor binary")
    ap.add_argument("--checker", type=_executable, help="fzn_drcp_check binary")

    def _enum_csv(enum):
        def parse(s: str) -> list:
            vals = s.split(",")
            assert set(vals) <= set(enum), f"{s}: choose from {','.join(enum)}"
            return [enum(v) for v in vals]
        return parse
    for col, enum in DIMS.items():
        values = ",".join(enum)
        ap.add_argument(f"--{col.replace('_', '-')}", type=_enum_csv(enum), default=list(enum),
                        metavar=values, help=f"comma-separated {col} (default: {values})")

    ap.add_argument("--pdf", type=lambda s: s and Path(s), default=None,
                    help='waterfall PDF path (default <input>.waterfall.pdf; "" to skip; one per problem)')
    return ap.parse_args(argv)


def main() -> None:
    args = parse_args()
    tools = Tools(args.solver, args.processor, args.checker)
    configs = list(configurations(args.input, args.repetitions, args.proof_type, args.mode, args.format, tools, args.max_rss))
    rows = asyncio.run(benchmark(configs, args.jobs))
    for path in args.input:
        if path.suffix == ".jsonl":
            rows += [json.loads(line) for line in path.read_text().splitlines()]

    assert rows, "no data: no inputs to benchmark or load"
    df = categorize(pd.DataFrame(rows).astype({"input": str}), list(dict.fromkeys(str(r["input"]) for r in rows)))
    dims = ["input"] + list(DIMS)
    print("\n# mean wall seconds per phase\n"
          + df.pivot_table("elapsed", dims, "phase", aggfunc="mean", observed=True).round(2).to_string(),
          file=sys.stderr)
    if args.pdf != "":
        problems = list(df.groupby("input", observed=True, sort=False))
        for q, sub in problems:
            dest = args.pdf or args.input[0].with_suffix(".waterfall.pdf") if len(problems) == 1 \
                else Path(str(q)).with_suffix(".waterfall.pdf")
            waterfall(sub, dest)


if __name__ == "__main__":
    main()
