BENCH_VENV := benchmark/.venv

BENCH_FZN := $(patsubst %.fzn.gz,%.fzn,$(wildcard benchmark/fzn/*.fzn.gz))

# Create the benchmark venv and install bench.py / compare.py's dependencies.
.PHONY: init
init:
	python3 -m venv $(BENCH_VENV)
	$(BENCH_VENV)/bin/pip install numpy pandas matplotlib tabulate scipy

benchmark/fzn/%.fzn: benchmark/fzn/%.fzn.gz
	gunzip -kf $<

.PHONY: decompress-fzn-corpus
decompress-fzn-corpus: $(BENCH_FZN)
