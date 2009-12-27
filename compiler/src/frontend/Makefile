BUILD = ../build
BIN = ../bin

.PHONY: all
all: lml.lex.sml lml.grm.sig lml.grm.sml

.PHONY: clean
clean:
	../../bin/clean

lml.lex.sml: lml.lex
	rm -rf lml.lex.sml
	mllex lml.lex
	chmod -w lml.lex.sml

lml.grm.sig lml.grm.sml: lml.grm
	rm -f lml.grm.*
	mlyacc lml.grm
	chmod -w lml.grm.*


