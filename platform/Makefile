ROOT    := ..
MODULES := AutoSepExt PreAutoSep \
           Util \
           AutoSep RecPred \
           Malloc \
           Bags Queue Scheduler Thread \
           Bootstrap SinglyLinkedList \
           tests/LinkTest tests/BabyThread tests/BabyThreadDriver tests/Yield tests/Spawn tests/ListBuilder

VS      := $(MODULES:%=%.v)

.PHONY: coq clean

coq: Makefile.coq
	$(MAKE) -f Makefile.coq

Makefile.coq: Makefile $(VS)
	coq_makefile -R $(ROOT)/src Bedrock -I tests \
		     $(VS) -o Makefile.coq

clean:: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq .depend
