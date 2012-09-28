ROOT    := ..
MODULES := Conditional Lambda Wrap Arr \
           AutoSepExt PreAutoSep \
           For AutoSep \
           LemmaTests \
           Baby TrivialMem TrivialMem2 ConditionalTest LambdaTest \
           Indir Factorial Swap TrivialArray \
           Pair SinglyLinkedList \
           Malloc \
           Sets ListSet TreeSet \
           Bags Queue \
           Memoize

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
