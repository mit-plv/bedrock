ROOT    := ..
MODULES := AutoSepExt AutoSep LemmaTests \
           Baby TrivialMem TrivialMem2 Indir Factorial Swap TrivialArray \
           Pair SinglyLinkedList \
           Malloc \
           Sets ListSet TreeSet

VS      := $(MODULES:%=%.v)

.PHONY: coq clean

coq: Makefile.coq
	COQC='time -f "%u user,%e real,%M mem" coqc' $(MAKE) -f Makefile.coq

Makefile.coq: Makefile $(VS)
	coq_makefile -R $(ROOT)/src Bedrock \
		     $(VS) -o Makefile.coq

clean:: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq .depend
