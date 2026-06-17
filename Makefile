BENCH_VENV := benchmark/.venv

# Create the benchmark venv and install bench.py's Python dependencies.
.PHONY: init
init:
	python3 -m venv $(BENCH_VENV)
	$(BENCH_VENV)/bin/pip install numpy pandas matplotlib scipy
