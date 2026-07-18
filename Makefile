BENCH_VENV := benchmark/.venv
DRCP_PROTO := lib/drcp/drcp-protobuf-schema/drcp_proto.proto
PUMPKIN_PROTO_URL := https://raw.githubusercontent.com/consol-lab/pumpkin/main/drcp-format/schema/drcp.proto

BENCH_FZN := $(patsubst %.fzn.gz,%.fzn,$(wildcard benchmark/fzn/*.fzn.gz))

$(DRCP_PROTO): FORCE
	wget -O $(DRCP_PROTO) $(PUMPKIN_PROTO_URL)
	sed -i 's|/\*`\([^`]*\)`\*/|\1|g' $(DRCP_PROTO)

FORCE:

# Create the benchmark venv and install bench.py / compare.py's dependencies.
.PHONY: init
init:
	python3 -m venv $(BENCH_VENV)
	$(BENCH_VENV)/bin/pip install numpy pandas matplotlib tabulate scipy

benchmark/fzn/%.fzn: benchmark/fzn/%.fzn.gz
	gunzip -kf $<

.PHONY: decompress-fzn-corpus
decompress-fzn-corpus: $(BENCH_FZN)
