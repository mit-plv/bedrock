ROOT    := ..
MODULES := AutoSep LemmaTests Allocated \
           Baby TrivialMem TrivialMem2 Indir Factorial Swap WordArith TrivialArray \
           Pair SinglyLinkedList \
           Malloc \
           Sets TreeSet

VS      := $(MODULES:%=%.v)

.PHONY: coq clean

coq: Makefile.coq
	COQC='time coqc' $(MAKE) -f Makefile.coq

Makefile.coq: Makefile $(VS)
	coq_makefile -R $(ROOT)/src Bedrock \
		     $(VS) -o Makefile.coq

clean:: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq .depend
