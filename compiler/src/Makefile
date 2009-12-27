BIN = ../bin

SOURCES =			\
	frontend/*.sml	\
	frontend/*.sig	\
	trace/*.sml	\
	trace/*.sig	\
	types/*.sig	\
	types/*.sml	\
	lib/*.sml	\
	lib/*.sig	\
	spec/*.sml	\
	spec/*.sig	\
	debug.sml	\
	lml.sml		\
	lml.mlb


.PHONY: all $(SOURCES)
all: $(BIN)/lml
.PHONY: clean
clean:
	../../bin/clean

frontend/lml.grm.sig frontend/lml.grm.sml frontend/lml.lex.sml: frontend/lml.grm frontend/lml.lex
	mllex frontend/lml.lex
	mlyacc frontend/lml.grm

spec/specl.grm.sig spec/specl.grm.sml spec/specl.lex.sml: spec/specl.grm spec/specl.lex
	mllex spec/specl.lex
	mlyacc spec/specl.grm

$(BIN)/lml: $(SOURCES) 
	mlton -output $(BIN)/lml lml.mlb


