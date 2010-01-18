BIN = ../bin

SOURCES =			\
	frontend/ml.lex.sml \
	frontend/frontend.mlb \
	frontend/*.sml	\
	types/*.sml	\
	types/types.mlb \
	ast/*.sml	\
	ast/ast.mlb \
	lib/*.sml	\
	lib/lib.mlb \
	codegen/*.sml \
	basis/*.sml \
	basis/basis.mlb \
	codegen/codegen.mlb \
	optimiser/*.sml	\
	optimiser/optimiser.mlb \
	debug.sml	\
	ml2pp0.sml		\
	ml2pp0_top.mlb \
	ml2pp0_bottom.mlb \
	lib/cvc3/cvc3.o


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

ml2pp0.mlb: ml2pp0_top.mlb ml2pp0_bottom.mlb lib/lib.mlb ast/ast.mlb basis/basis.mlb frontend/frontend.mlb codegen/codegen.mlb optimiser/optimiser.mlb types/types.mlb
	cat ml2pp0_top.mlb lib/lib.mlb ast/ast.mlb types/types.mlb basis/basis.mlb frontend/frontend.mlb optimiser/optimiser.mlb codegen/codegen.mlb ml2pp0_bottom.mlb > ml2pp0.mlb

lib/cvc3/cvc3.o: lib/cvc3/cvc3.cpp
	make -C lib

$(BIN)/ml2pp0: ml2pp0.mlb $(SOURCES) $(BIN)
	mlton -default-ann 'allowFFI true' -output $(BIN)/ml2pp0 ml2pp0.mlb lib/cvc3/cvc3.o


