BIN = ../bin

SOURCES =			\
	frontend/ml.lex.sml \
	frontend/*.sml	\
	types/*.sml	\
	ast/*.sml	\
	lib/*.sml	\
	codegen/*.sml \
	optimiser/*.sml	\
	debug.sml	\
	ml2pp0.sml		\
	ml2pp0.mlb


.PHONY: all 
all: $(BIN)/ml2pp0 
.PHONY: clean

$(BIN):
	mkdir -p $(BIN)

clean:
	../../bin/clean

frontend/ml.grm.sml frontend/ml.lex.sml: frontend/ml.lex frontend/ml.grm
	mllex frontend/ml.lex
	mlyacc frontend/ml.grm

$(BIN)/ml2pp0: $(SOURCES) $(BIN)
	mlton -output $(BIN)/ml2pp0 ml2pp0.mlb


