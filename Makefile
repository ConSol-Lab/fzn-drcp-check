BENCH_VENV := benchmark/.venv

# Create the benchmark venv and install bench.py / compare.py's dependencies.
.PHONY: init
init:
	python3 -m venv $(BENCH_VENV)
	$(BENCH_VENV)/bin/pip install numpy pandas matplotlib tabulate scipy
