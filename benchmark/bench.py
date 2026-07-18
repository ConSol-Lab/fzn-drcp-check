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

from collections.abc import Callable, Iterable, Iterator
from dataclasses import asdict, dataclass, field, fields
from enum import StrEnum
from functools import cache, cached_property
from itertools import product
from pathlib import Path
from typing import ClassVar, cast

import numpy as np
import pandas as pd

class ProofType(StrEnum):
    NONE, SCAFFOLD, FULL = "none", "scaffold", "full"

class Mode(StrEnum):
    NONE, BATCH, INCREMENTAL, STREAMING = "none", "batch", "incremental", "streaming"

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

class Checker(StrEnum):
    NONE, RUST, ROCQ = "none", "rust", "rocq"

class Phase(StrEnum):
    SOLVE, PROCESS, CHECK = "solve", "process", "check"

DIMS = {"proof_type": ProofType, "mode": Mode, "format": Format, "checker": Checker}
PROOF_SUFFIXES = (".drcp", ".bin")

type ConfigKey = tuple[str, ...]
type Row = dict[str, object]

@cache
def which(name: str) -> str:
    assert (p := shutil.which(name)), f"need `{name}` on PATH"
    return p

def log(*a) -> None:
    print(*a, file=sys.stderr, flush=True)

GNU_TIME_FMT = {"elapsed": "%e", "user": "%U", "sys": "%S", "peak_rss": "%M", "majflt": "%F",
                "minflt": "%R", "fsin": "%I", "fsout": "%O", "waits": "%w", "preempts": "%c"}
GNU_TIME_FMT_STR = " ".join(f"{k}={c}" for k, c in GNU_TIME_FMT.items())

@dataclass
class Tools:
    """The solver/processor/checker binaries."""
    solver: Path
    processor: Path
    rocq_checker: Path
    rust_checker: Path

@dataclass
class Stage:
    phase: Phase
    cmd: list[str | Path]
    cpu: int
    consumes: Path
    produces: Path | None
    wd: Path
    max_rss: int | None
    concurrent: bool

    @property
    def stat(self) -> Path:
        """Where GNU time writes this stage's measurement."""
        return self.wd / f"{self.phase}.stat"

    async def spawn(self) -> asyncio.subprocess.Process:
        """Launch this stage under GNU time, on `cpu`, with `max_rss`."""
        cap = [which("prlimit"), f"--as={self.max_rss}", "--"] if self.max_rss is not None else []
        argv = [which("taskset"), "-c", str(self.cpu), *cap, which("time"),
                "-f", GNU_TIME_FMT_STR, "-o", str(self.stat), "--", *self.cmd]
        log(f"[{time.strftime('%H:%M:%S')}] {' '.join(map(str, self.cmd))}")
        return await asyncio.create_subprocess_exec(*argv, stdout=asyncio.subprocess.DEVNULL,
                                                    stderr=asyncio.subprocess.DEVNULL)

@dataclass
class StageResult:
    """A finished pipeline stage."""
    phase: Phase
    concurrent: bool # overlaps the previous phase
    elapsed: float # process wall
    user: float # user CPU seconds
    sys: float # system/kernel CPU seconds
    peak_rss: int # peak resident set, bytes
    majflt: int # major page faults
    minflt: int # minor page faults
    fsin: int # filesystem block inputs
    fsout: int # filesystem block outputs
    waits: int # voluntary context switches
    preempts: int # involuntary context switches
    returncode: int
    produces_bytes: int | None

    @staticmethod
    def from_gnutime(stage: Stage, stats: str, returncode: int) -> "StageResult":
        """Build from GNU time's `stats` text."""
        f = dict(tok.split("=", 1) for tok in stats.split() if "=" in tok)
        counters = {fld.name: cast(type, fld.type)(f[fld.name]) for fld in fields(StageResult)
                    if fld.name in GNU_TIME_FMT}
        counters["peak_rss"] *= 1024 # %M is KiB
        pb = stage.produces.stat().st_size if stage.produces and stage.produces.is_file() else None
        return StageResult(stage.phase, stage.concurrent, returncode=returncode, produces_bytes=pb, **counters)

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

    def as_json(self) -> list[Row]:
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
    checker: Checker
    repetition_idx: int
    max_rss: int | None # rss cap in bytes

    @property
    def key(self) -> ConfigKey:
        return config_key(vars(self))

    @property
    def is_proof(self) -> bool:
        """Whether `input` is a pre-generated proof."""
        return self.input.suffix in PROOF_SUFFIXES

    def stages(self, wd: Path, cpu_a: int, cpu_b: int) -> tuple[list[Stage], list[Stage]]:
        """Build the pipeline."""
        def stage(phase, cmd, cpu, consumes, produces, concurrent=False):
            return Stage(phase, cmd, cpu, consumes, produces, wd, self.max_rss, concurrent)
        if self.proof_type is ProofType.NONE:
            return [stage(Phase.SOLVE, [self.tools.solver, self.input], cpu_a, self.input, None)], []
        flags = self.format.flags
        sflag = self.mode.flags * (self.checker is Checker.ROCQ)
        checker = getattr(self.tools, f"{self.checker}_checker")
        if self.is_proof:
            cmd = [checker, *sflag, *flags, self.input.with_suffix(".fzn"), self.input]
            return [stage(Phase.CHECK, cmd, cpu_a, self.input, None)], []
        full = (wd / "full").with_suffix(self.format.suffix)
        if self.mode.pipelined:
            full = full.with_name(full.name + ".fifo")
        check = stage(Phase.CHECK, [checker, *sflag, *flags, self.input, full],
                      cpu_b if self.mode.pipelined else cpu_a, full, None, concurrent=self.mode.pipelined)
        if self.proof_type is ProofType.SCAFFOLD:
            scaffold = (wd / "scaffold").with_suffix(self.format.suffix)
            flat = [stage(Phase.SOLVE, [self.tools.solver, self.input, *flags, "--proof-path", scaffold], cpu_a, self.input, scaffold),
                    stage(Phase.PROCESS, [self.tools.processor, *flags, self.input, scaffold, full], cpu_a, scaffold, full),
                    check]
        else:
            flat = [stage(Phase.SOLVE, [self.tools.solver, self.input, "--proof-type", "full", *flags, "--proof-path", full], cpu_a, self.input, full),
                    check]
        # pipelining overlaps producer and check through the FIFO
        return (flat[:-2], flat[-2:]) if self.mode.pipelined else (flat, [])

    async def run(self, cpu_a: int, cpu_b: int) -> Run:
        """Run the sequential prefix, then the concurrent group."""
        with tempfile.TemporaryDirectory(prefix="bench.") as tmp:
            prefix, overlap = self.stages(Path(tmp), cpu_a, cpu_b)
            for stage in overlap:
                if stage.concurrent:
                    os.mkfifo(stage.consumes)
            sequential = [await self.measure(s, await s.spawn()) for s in prefix] # wait for each thread sequentially
            running = [(s, await s.spawn()) for s in overlap] # spawn all together without waiting
            concurrent = [await self.measure(s, proc) for s, proc in running]
        return Run(self, sequential + concurrent)

    async def measure(self, stage: Stage, proc: asyncio.subprocess.Process) -> StageResult:
        """Reap `stage` and read GNU time's output."""
        returncode = await proc.wait()
        stats = stage.stat.read_text(encoding="utf-8")
        return StageResult.from_gnutime(stage, stats, returncode)

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
    assert ncpu > 1
    rot = cpu_rotation(ncpu)
    workers = max(1, min(jobs // 2, ncpu // 2))
    return [(rot[2 * k], rot[2 * k + 1]) for k in range(workers)]

def config_key(d: dict) -> ConfigKey:
    return tuple(str(d[f]) for f in ("input", "proof_type", "mode", "format", "checker", "repetition_idx"))

def read_jsonl(path: Path) -> list[Row]:
    return [json.loads(l) for l in filter(str.strip, path.read_text(encoding="utf-8").splitlines())]

def configurations(inputs: list[Path], reps: int, types: list[ProofType], modes: list[Mode],
                   formats: list[Format], checkers: list[Checker], tools: Tools,
                   max_rss: int | None) -> Iterator[BenchmarkConfiguration]:
    """Valid configurations in inputs × reps × types × modes × formats × checkers."""
    for inp, rep, pt, mode, fmt, checker in product(inputs, range(reps), types, modes, formats, checkers):
        if inp.suffix == ".jsonl": # Skip prerecorded results
            continue
        none = [pt is ProofType.NONE, mode is Mode.NONE, checker is Checker.NONE]
        if any(none) != all(none):
            continue
        if inp.suffix in PROOF_SUFFIXES: # Skip irrelevant runs for pre-recorded proofs
            if pt is not ProofType.FULL or fmt.suffix != inp.suffix or mode is Mode.STREAMING:
                continue
        if checker is Checker.RUST and mode is Mode.BATCH:
            continue
        yield BenchmarkConfiguration(tools, inp.resolve(), pt, mode, fmt, checker, rep, max_rss)

async def benchmark(configs: list[BenchmarkConfiguration], jobs: int, emit: Callable[[Row], None]) -> None:
    """Run `configs`."""
    work, done, n = iter(configs), 0, len(configs)

    async def worker(cpu_a: int, cpu_b: int) -> None:
        nonlocal done
        for cfg in work:
            run = await cfg.run(cpu_a, cpu_b)
            for row in run.as_json():
                emit(row)
            done += 1
            log(f"[{done}/{n}] {run.summary}")

    ncpu = os.process_cpu_count() or 2
    await asyncio.gather(*(worker(a, b) for a, b in cpu_pairs(jobs, ncpu)))

@dataclass
class Waterfall:
    THINSP: ClassVar[str] = " " # thin punctuation space
    _IEC: ClassVar[list[str]] = ["B", "KiB", "MiB", "GiB", "TiB", "PiB"]
    LABEL_HEADROOM: ClassVar[float] = 1.5 # widen each axis past the longest bar for its inline value label
    MODE_X: ClassVar[int] = -4 # x offsets (pt) for the mode / proof-type / format labels
    TYPE_X: ClassVar[int] = -54
    FMT_X: ClassVar[int] = -78
    ROW_H: ClassVar[float] = 0.24
    MARGIN: ClassVar[float] = 2.0
    CHECKER_COLOR: ClassVar[dict[Checker, str]] = {Checker.ROCQ: "#ff540a", Checker.RUST: "#b7410e"} # Rocq orange / Rust rust
    CHK_GAP: ClassVar[float] = 0.4 # gap between a scenario's two checker waterfalls
    SCEN_GAP: ClassVar[float] = 1.1 # gap between scenarios
    df: pd.DataFrame

    def __post_init__(self) -> None:
        import matplotlib
        from matplotlib.colors import to_hex
        from matplotlib.ticker import EngFormatter
        matplotlib.rcParams.update({"font.family": "sans-serif",
                                    "font.sans-serif": ["Fira Sans", "DejaVu Sans"],
                                    "axes.axisbelow": True})
        self.df = categorize(self.df, self.df["input"].unique()) # enum-ordered axes
        self.color = dict(zip(Phase, map(to_hex, matplotlib.color_sequences["petroff10"])))
        self.color |= {f"check ({c.capitalize()})": col for c, col in self.CHECKER_COLOR.items()}
        self.ES = EngFormatter("s", places=1, sep=self.THINSP) # seconds with fixed precision
        self.sec_formatter = EngFormatter("s", sep=self.THINSP) # seconds with auto precision

    @staticmethod
    def _boot_ci(vals) -> tuple[float, float] | None:
        """95% BCa-bootstrap CI for the mean."""
        from scipy.stats import bootstrap
        v = np.asarray(vals, float)
        v = v[~np.isnan(v)]
        if v.size < 2 or np.ptp(v) == 0:
            return None
        ci = bootstrap((v,), np.mean, confidence_level=0.95, n_resamples=10000, rng=0).confidence_interval
        return float(ci.low), float(ci.high)

    @classmethod
    def _iec_unit(cls, n) -> tuple[int, str]:
        """Compute the divisor and unit label to render `n` bytes in IEC units."""
        i = min((int(n).bit_length() - 1) // 10, len(cls._IEC) - 1) if n >= 1 else 0
        return 1 << (10 * i), cls._IEC[i]

    @classmethod
    def iec_bytes(cls, n, places: int = 1) -> str:
        """Format `n` bytes in IEC units (KiB, MiB, GiB, ...)."""
        n = max(float(n), 0.0)
        div, unit = cls._iec_unit(n)
        return f"{n / div:.{places}f}{cls.THINSP}{unit}"

    @classmethod
    def set_binary_byte_ticks(cls, xaxis, vmax, target: int = 6) -> None:
        """Place ticks at round multiples of KiB, MiB, GiB, ...."""
        from matplotlib.ticker import FuncFormatter, MultipleLocator
        q = max(1, int(np.ceil(max(1.0, vmax) / target)))
        step = 1 << (q - 1).bit_length() # smallest power of two >= q
        div, unit = cls._iec_unit(step)
        xaxis.set_major_locator(MultipleLocator(step))
        xaxis.set_major_formatter(FuncFormatter(lambda x, pos: f"{x / div:.0f}{cls.THINSP}{unit}"))

    @classmethod
    def _ci_annot(cls, mean: float, lo: float, hi: float, fmt: Callable[[float], str]) -> str:
        """Render ``mean^{+hi}_{-lo}`` as mathtext, feeding numbers to `fmt`."""
        if np.isnan(hi):
            return fmt(mean)
        def t(x: float) -> str:
            num, unit = fmt(max(0.0, x)).split(cls.THINSP)
            return rf"{num}\,\mathrm{{{unit}}}"
        return f"${t(mean)}^{{+{t(hi - mean)}}}_{{-{t(mean - lo)}}}$"

    @staticmethod
    def _stack(g: pd.DataFrame) -> pd.DataFrame:
        """Reconstruct each phase's start and memory base."""
        g = g.sort_values("phase")
        conc = g["concurrent"]
        assert conc.dtype == bool
        prev_wall = g["wall"].shift(1).fillna(0.0)
        prev_rss = g["peak_rss"].shift(1).fillna(0.0)
        return g.assign(start=(prev_wall * ~conc).cumsum(),
                        mstart=(prev_rss * conc).cumsum())

    def _label_facet(self, row, fm, s) -> None:
        ax = row[0]
        gb = s.groupby(["proof_type", "mode"], observed=True)
        scen = gb["y"].mean()
        tot = {k: ((g["start"] + g["wall"]).max() - g["start"].min(),
                   (g["mstart"] + g["peak_rss"]).max()) # peak co-resident RSS
               for k, g in gb}
        ax.set_yticks(scen.values, [""] * len(scen)) # placeholders (labels drawn below)
        from matplotlib.transforms import offset_copy
        tr = ax.get_yaxis_transform()
        at = lambda dx: offset_copy(tr, fig=ax.figure, x=dx, y=0, units="points")
        mode_t, pt_t, fmt_t = at(self.MODE_X), at(self.TYPE_X), at(self.FMT_X)
        for (pt, m), y in scen.items():
            t, mem = tot[(pt, m)]
            ax.text(0, y, m, transform=mode_t, ha="right", va="bottom", fontsize=7)
            ax.text(0, y, f"{self.ES(t)}, {self.iec_bytes(mem)}", transform=mode_t, ha="right", va="top", fontsize=5.5, color="0.4")
        span = s.groupby("proof_type", observed=True)["y"].agg(["min", "max", "mean"]).sort_values("max", ascending=False)
        prev = None
        for pt, r in span.iterrows():
            ax.text(0, r["mean"], str(pt), transform=pt_t, ha="right", va="center", fontweight="bold", fontsize=8)
            if prev is not None:
                for a in row:
                    a.axhline((prev + r["max"]) / 2, color="0.85", lw=.6, zorder=0)
            prev = r["min"]
        ax.text(0, s["y"].mean(), fm, transform=fmt_t, ha="center", va="center", rotation=90, fontweight="bold", fontsize=9)
        for a in row:
            a.tick_params(left=False)
        row[1].tick_params(labelleft=False)

    def _compute_y(self, s) -> pd.DataFrame:
        scn = s.groupby(["proof_type", "mode"], observed=True, sort=False).ngroup()
        first = s.groupby(["proof_type", "mode", "checker"], observed=True, sort=False).cumcount() == 0
        gap = np.where(first & scn.ne(scn.shift()), self.SCEN_GAP, np.where(first, self.CHK_GAP, 0.0))
        gap[0] = 0.0
        return s.assign(y=-(np.arange(len(s)) + gap.cumsum()))

    def _draw_facet(self, axs_row, fm, s) -> None:
        clr = s["phase"].map(self.color)
        aw, am = axs_row
        aw.set_ylim(s["y"].min() - 0.6, s["y"].max() + 0.6) # trim the autoscaled y-margin
        aw.barh(s.y, s.cpu, left=s.start, height=1, color=clr)
        aw.barh(s.y, s.wall - s.cpu, left=s.start + s.cpu, height=1, color=clr, alpha=.3, hatch="///", ec=clr, lw=0)
        am.barh(s.y, s.peak_rss, left=s.mstart, height=1, color=clr)
        for ax, base, val, lo, hi in [(aw, "start", "wall", "lo_t", "hi_t"),
                                      (am, "mstart", "peak_rss", "lo_m", "hi_m")]:
            if not (e := s[s[hi].notna()]).empty: # rows with a CI to draw
                xerr = np.clip([e[val] - e[lo], e[hi] - e[val]], 0, None)
                ax.errorbar(e[base] + e[val], e["y"], xerr=xerr,
                            fmt="none", ecolor="0.2", capsize=1.5, lw=.7)
        for b in s.itertuples():
            sz = f" → {self.iec_bytes(b.produces_bytes)}" if not np.isnan(b.produces_bytes) else ""
            aw.text(b.start + b.t_label_x, b.y, f"  {b.phase}: {self._ci_annot(b.wall, b.lo_t, b.hi_t, self.ES)}{sz}", va="center", fontsize=6)
            am.text(b.mstart + b.m_label_x, b.y, f"  {self._ci_annot(b.peak_rss, b.lo_m, b.hi_m, self.iec_bytes)}", va="center", fontsize=6)
        self._label_facet(axs_row, fm, s)

    def render(self, dest: Path) -> None:
        from matplotlib.figure import Figure
        from matplotlib.patches import Patch

        def agg(g):
            lt, ht = self._boot_ci(g["elapsed"]) or (np.nan, np.nan)
            lm, hm = self._boot_ci(g["peak_rss"]) or (np.nan, np.nan)
            assert g["concurrent"].nunique() == 1
            return pd.Series({"wall": g["elapsed"].mean(), "cpu": g["cpu"].mean(), "peak_rss": g["peak_rss"].mean(),
                              "concurrent": g["concurrent"].iloc[0], "produces_bytes": g["produces_bytes"].astype(float).mean(),
                              "lo_t": lt, "hi_t": ht, "lo_m": lm, "hi_m": hm})

        df = self.df.assign(cpu=self.df[["user", "sys"]].sum(axis=1, min_count=1))
        scen = ["format", "proof_type", "mode", "checker"]
        a = (df.groupby(scen + ["phase"], observed=True)[["elapsed", "cpu", "peak_rss", "concurrent", "produces_bytes"]]
             .apply(agg).reset_index())
        a = pd.concat([self._stack(g) for _, g in a.groupby(scen, observed=True)], ignore_index=True)
        a["phase"] = np.where(a["phase"] == Phase.CHECK,
                              "check (" + a["checker"].astype(str).str.capitalize() + ")", a["phase"].astype(str))
        a["t_label_x"], a["m_label_x"] = a.hi_t.fillna(a.wall), a.hi_m.fillna(a.peak_rss)
        fmts = a["format"].sort_values().unique()
        fig = Figure(figsize=(12, self.ROW_H * len(a) + self.MARGIN))
        fig.set_layout_engine("constrained", w_pad=0.04, h_pad=0.04, wspace=0.02, hspace=0.06)
        axs = fig.subplots(len(fmts), 2, sharex="col", sharey="row", squeeze=False)
        for r, fm in enumerate(fmts):
            self._draw_facet(axs[r], fm, self._compute_y(a[a["format"] == fm].copy()))
        rss_max = max(1.0, (a.mstart + a.m_label_x).max() * self.LABEL_HEADROOM)
        wall_max = max(1.0, (a.start + a.t_label_x).max() * self.LABEL_HEADROOM)
        for ax in axs[:, 0]:
            ax.xaxis.set_major_formatter(self.sec_formatter)
        for ax in axs[:, 1]:
            self.set_binary_byte_ticks(ax.xaxis, rss_max)
        for ax in axs.ravel():
            ax.tick_params(axis="x", labelsize=7, labelbottom=True) # repeat x labels on the top row too
        axs[0][0].set_title("wall-clock", fontsize=9)
        axs[0][1].set_title("peak RSS", fontsize=9)
        axs[0][0].set_xlim(0, wall_max)
        axs[0][1].set_xlim(0, rss_max)
        present = set(self.df["checker"])
        checks = [f"check ({c.capitalize()})" for c in self.CHECKER_COLOR if c in present]
        fig.legend(handles=[Patch(color=self.color[p], label=p) for p in [Phase.SOLVE, Phase.PROCESS, *checks]] +
                   [Patch(facecolor="0.7", hatch="///", ec="0.4", label="waiting (wall − CPU)")],
                   ncol=5, loc="outside lower center", fontsize=7, frameon=False,
                   title=r"bars = mean   ·   error bar and $x^{+hi}_{-lo}$ = 95% bootstrap CI", title_fontsize=7)
        ipath = Path(str(self.df["input"].iloc[0]))
        fig.suptitle(f"{ipath.parent.name}/{ipath.name}" if ipath.parent.name else ipath.name,
                     fontsize=11, fontweight="bold")
        fig.savefig(dest, bbox_inches="tight")
        log(f"→ {dest}")

def parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    ap = argparse.ArgumentParser(description="Benchmark and plot the Pumpkin -> verified-checker pipeline.")
    ap.add_argument("-n", "--repetitions", type=int, default=5, help="repetitions per query (default: 5)")
    ap.add_argument("-j", "--jobs", type=int, default=2, help="concurrency level (default: 2; >= 2 for streaming)")
    ap.add_argument("--max-rss", type=lambda s: int(s) << 20, default=None,
                    help="per-process memory cap in MiB (an address-space limit via prlimit --as)")
    ap.add_argument("--resume", action="store_true",
                    help="skip configurations already recorded in each input's <input>.jsonl, and append to it")

    def _input(s: str) -> Path:
        assert (p := Path(s)).suffix in (".fzn", ".jsonl", *PROOF_SUFFIXES), \
            f"{p}: expected .fzn (solve+check), .drcp/.bin (check), or .jsonl (plot only)"
        return p
    ap.add_argument("input", type=_input, nargs="+", help=".fzn, .drcp, .bin, or .jsonl")

    def _executable(s: str) -> Path:
        assert os.access(p := Path(s), os.X_OK), f"{p}: not executable"
        return p
    ap.add_argument("--solver", type=_executable, default=Path("pumpkin-solver"), help="pumpkin-solver binary")
    ap.add_argument("--processor", type=_executable, default=Path("pumpkin-proof-processor"), help="pumpkin-proof-processor binary")
    ap.add_argument("--rocq-checker", type=_executable, default=Path("drcpcheck"), help="verified drcpcheck binary")
    ap.add_argument("--rust-checker", type=_executable, default=Path("pumpkin-checker"), help="native pumpkin-checker binary")

    def _enum_csv(enum: type[StrEnum]):
        def parse(s: str) -> list:
            vals = s.split(",")
            assert set(vals) <= set(enum), f"{s}: choose from {','.join(enum)}"
            return [enum(v) for v in vals]
        return parse
    for col, enum in DIMS.items():
        default = [Checker.NONE, Checker.ROCQ] if enum is Checker else list(enum)
        ap.add_argument(f"--{col.replace('_', '-')}s", type=_enum_csv(enum), default=default,
                        metavar=",".join(enum), help=f"comma-separated {col}s (default: {','.join(default)})")

    ap.add_argument("--pdf", action=argparse.BooleanOptionalAction, default=True,
                    help="render per-problem waterfall PDFs (default: on; --no-pdf to skip)")
    return ap.parse_args(argv)

def categorize(df: pd.DataFrame, inputs: Iterable[str]) -> pd.DataFrame:
    """Order every categorical column by its enum's definition order."""
    for col, order in {"input": inputs, "phase": Phase, **DIMS}.items():
        df[col] = pd.Categorical(df[col], [str(v) for v in order], ordered=True)
    return df

@dataclass
class OutputFile:
    input: Path
    resume: bool
    rows: list[Row] = field(init=False, default_factory=list)
    skipped: set[ConfigKey] = field(init=False, default_factory=set)

    def __post_init__(self) -> None:
        if not (self.read_existing and self.path.exists()):
            return
        rows = read_jsonl(self.path)
        if self.is_plot_only:
            self.rows = rows
            return
        self.skipped = {config_key(r) for r in rows if r["phase"] == Phase.CHECK}
        self.rows = [r for r in rows if config_key(r) in self.skipped] # drop partial traces (interrupted runs)

    @property
    def is_plot_only(self) -> bool:
        return self.input.suffix == ".jsonl"

    @property
    def read_existing(self) -> bool:
        return self.resume or self.is_plot_only

    @property
    def path(self) -> Path:
        return self.input if self.is_plot_only else self.input.with_name(self.input.name + ".jsonl")

    @cached_property
    def file(self):
        f = open(self.path, "w", encoding="utf-8")
        for row in self.rows: # Re-emit kept rows
            print(json.dumps(row, default=str), file=f)
        f.flush()
        return f

    def write(self, line: str) -> None:
        print(line, file=self.file, flush=True)
        self.rows.append(json.loads(line))

    def close(self) -> None:
        if "file" in self.__dict__:
            self.file.close()
            del self.file

def main() -> None:
    args = parse_args()
    tools = Tools(args.solver, args.processor, args.rocq_checker, args.rust_checker)
    outs = {p.resolve(): OutputFile(p, args.resume) for p in args.input}
    done = set().union(*(o.skipped for o in outs.values())) if args.resume else set()
    if args.resume:
        log(f"resume: skipping {len(done)} already-recorded configurations")
    configs = [c for c in configurations(args.input, args.repetitions, args.proof_types, args.modes,
                                         args.formats, args.checkers, tools, args.max_rss) if c.key not in done]
    log(f"running {len(configs)} configurations")

    def emit(row: Row) -> None:
        line = json.dumps(row, default=str)
        print(line)
        if o := outs.get(row["input"]):
            o.write(line)
    try:
        asyncio.run(benchmark(configs, args.jobs, emit))
    finally:
        for o in outs.values():
            o.close()

    with_rows = [o for o in outs.values() if o.rows]
    rows = [r for o in with_rows for r in o.rows]
    assert rows, "no data: no inputs to benchmark or load"
    df = pd.DataFrame(rows).astype({"input": str})
    df = categorize(df, df["input"].unique())
    log("\n# mean wall seconds per phase\n"
        + df.pivot_table("elapsed", ["input"] + list(DIMS), "phase", aggfunc="mean", observed=True).round(2).to_string())

    if args.pdf:
        for o in with_rows:
            group = df[df["input"].isin({r["input"] for r in o.rows})]
            Waterfall(group.copy()).render(o.path.with_suffix(".pdf"))

if __name__ == "__main__":
    main()
