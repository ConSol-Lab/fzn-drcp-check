#!/bin/bash

set -e

shopt -s globstar

dune build

for f in $1/**/*.fzn; do
    ./_build/default/bin/main.exe $f
done
