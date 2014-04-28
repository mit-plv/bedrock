ROOT    := ../..
MODULES := Logic Cancel PtsToEntail \
	AlgebraicDatatypes Statements Compile CompileModule \
	Depl \
	examples/Baby examples/Basic

VS      := $(MODULES:%=%.v)

.PHONY: coq clean

coq: Makefile.coq
	$(MAKE) -f Makefile.coq

COQARGS := -R $(ROOT)/src Bedrock -I .. -R . Depl

Makefile.coq: Makefile $(VS)
	coq_makefile $(COQARGS) $(VS) -o Makefile.coq

clean:: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq .depend
