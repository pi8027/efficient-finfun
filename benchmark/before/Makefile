include ./.deps

COQLIBS=-R . vass ${COQLIBS}
VOFILES=$(VFILES:.v=.vo)
GLOBFILES=$(VFILES:.v=.glob)

.DEFAULT_GOAL := all
.PHONY: all clean

all: ${VOFILES}

clean:
	rm -f .deps ${VOFILES} ${GLOBFILES}

.deps: ${VFILES}
	coqdep -c -w ${COQLIBS} ${VFILES} > .deps

%.vo %.glob: %.v
	coqc -q ${COQLIBS} $*
