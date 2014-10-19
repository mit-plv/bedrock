ROOT    := ..
MODULES := Conditional Lambda \
           AutoSepExt PreAutoSep \
           Wrap StreamParse ArrayQuery \
           AutoSep \
           LemmaTests \
           Baby TrivialMem TrivialMem2 Arr \
           ConditionalTest LambdaTest StreamParseTest ArrayQueryTest \
           Indir Factorial Swap TrivialArray \
           Pair SinglyLinkedList \
           Malloc \
           Sets ListSet TreeSet \
           Bags Queue \
           Memoize

VS      := $(MODULES:%=%.v)

.PHONY: coq clean

coq: Makefile.coq
	COQC='time $(COQBIN)coqc' $(MAKE) -f Makefile.coq

Makefile.coq: Makefile $(VS)
	$(COQBIN)coq_makefile -R $(ROOT)/src Bedrock \
		     $(VS) -o Makefile.coq

clean:: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq .depend
