#!/usr/bin/env bash
# Simple end-to-end pipeline
# Usage:  PUMPKIN=../Pumpkin-bin  ./e2e.sh  model.mzn  [data.dzn ...]    (needs minizinc on PATH)
set -u
P=${PUMPKIN:?set PUMPKIN to your Pumpkin build dir, e.g. ../Pumpkin-bin}
solver=$P/target/release/pumpkin-solver
proc=$P/target/release/pumpkin-proof-processor
checker=$(dirname "$0")/../_build/default/bin/main.exe
mzn=${1:?usage: PUMPKIN=... $0 model.mzn [data.dzn ...]}; shift

wd=$(mktemp -d); trap 'rm -rf "$wd"' EXIT; fzn=$wd/m.fzn; rc=0
verdict() { case $1 in 0) echo valid;; 1) echo invalid;; *) echo "error $1";; esac; }

minizinc --solver "$P/minizinc/pumpkin-for-proofs.msc" -c "$mzn" "$@" --fzn "$fzn"

for ext in bin drcp; do
  tag=$([ "$ext" = bin ] && echo binary || echo text)

  echo "== full / streaming / $tag"
  mkfifo "$wd/fifo.$ext"
  "$solver" "$fzn" --proof-type full --proof-path "$wd/fifo.$ext" >/dev/null & sp=$!
  "$checker" -s "$fzn" "$wd/fifo.$ext" >/dev/null; v=$?; wait "$sp"
  echo "   -> $(verdict "$v")"; [ "$v" = 0 ] || rc=1
  rm "$wd/fifo.$ext"

  echo "== scaffold+process / batch / $tag"
  "$solver" "$fzn" --proof-path "$wd/scaffold.$ext" >/dev/null
  "$proc" "$fzn" "$wd/scaffold.$ext" "$wd/proof.$ext" >/dev/null
  "$checker" "$fzn" "$wd/proof.$ext" >/dev/null; v=$?
  echo "   scaffold $(stat -c%s "$wd/scaffold.$ext")B, proof $(stat -c%s "$wd/proof.$ext")B -> $(verdict "$v")"
  [ "$v" = 0 ] || rc=1
done
exit $rc
