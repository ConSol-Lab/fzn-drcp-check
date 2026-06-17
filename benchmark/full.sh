#!/bin/bash
set -euo pipefail
cd "$(dirname "$0")"

make -C .. decompress-fzn-corpus

run() { local j=$1 cap=$2; shift 2; python3 bench.py "$@" -n "${REPS:-8}" -j "$j" --max-rss "$cap" --resume --no-pdf; }
fz() { for p in $*; do echo "fzn/$p.fzn"; done; }

scaffold_ok="market_split_u3_01 test-scheduling_2018_t30m10r10-5 gfd-schedule_2022_n60f7d50m30k10"
light="$scaffold_ok rcpsp_2013_12 rcpsp_2013_14 rcpsp-wet_2017_j30_1_3"
big="rcpsp-wet_2017_j30_43_10 racp_2020_j30_26_2"

run 4  8000  $(fz $light $big)  --proof-type none
run 4  8000  $(fz $scaffold_ok) --proof-type scaffold
run 4  20000 $(fz $light)       --proof-type full
run 4  24000 $(fz $big)         --proof-type full --mode incremental,streaming
run 2  56000 $(fz $big)         --proof-type full --mode batch

python3 bench.py fzn/*.fzn.jsonl
