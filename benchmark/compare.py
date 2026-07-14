#!/usr/bin/env python3
"""Print a before/after delta table for two bench.py runs.

    compare.py [--phase solve] --old before/*.jsonl --new after/*.jsonl
"""
import argparse
import sys
from pathlib import Path

import pandas as pd

sys.path.insert(0, str(Path(__file__).resolve().parent))
from bench import Format, Mode, Phase, read_jsonl  # noqa: E402

FMT = {str(Format.TEXT): "text", str(Format.BINARY): "bin"}
MODE = {str(Mode.BATCH): "batch", str(Mode.INCREMENTAL): "stream", str(Mode.STREAMING): "stream"}


def phase_means(paths: list[Path], phase: str) -> pd.DataFrame:
    df = pd.DataFrame(r for p in paths for r in read_jsonl(p))
    df = df[df["phase"] == phase]
    mode = df["format"].map(FMT) + " " + df["mode"].map(MODE) if phase == str(Phase.CHECK) else df["format"].map(FMT)
    df = df.assign(instance=df["input"].map(lambda s: Path(str(s)).stem),
                   mode=mode, m=df["peak_rss"] / (1 << 20))
    return df.groupby(["instance", "mode"], observed=True).agg(t=("elapsed", "mean"), m=("m", "mean"))


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--old", type=Path, nargs="+", required=True, help="baseline bench.py JSONL(s)")
    ap.add_argument("--new", type=Path, nargs="+", required=True, help="candidate bench.py JSONL(s)")
    ap.add_argument("--phase", choices=[str(p) for p in Phase], default=str(Phase.CHECK),
                    help="pipeline phase to compare (default: check)")
    args = ap.parse_args()

    d = phase_means(args.old, args.phase).join(phase_means(args.new, args.phase), lsuffix="<", rsuffix=">", how="inner")
    d["Δt"] = (d["t>"] - d["t<"]) / d["t<"] * 100
    d["Δm"] = (d["m>"] - d["m<"]) / d["m<"] * 100
    fmt = {"t<": "{:.2f}s", "t>": "{:.2f}s", "Δt": "{:+.0f}%",
           "m<": "{:.0f}MiB", "m>": "{:.0f}MiB", "Δm": "{:+.0f}%"}
    out = d.reset_index()[["instance", "mode", *fmt]].copy()
    for col, spec in fmt.items():
        out[col] = out[col].map(spec.format)
    print(out.to_markdown(index=False))


if __name__ == "__main__":
    main()
