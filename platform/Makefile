ROOT    := ..
MODULES := AutoSepExt PreAutoSep \
           Util \
           AutoSep \
           Malloc \
           Bags Queue Scheduler Thread \
           Bootstrap \
           tests/BabyThread

VS      := $(MODULES:%=%.v)

.PHONY: coq clean

coq: Makefile.coq
	$(MAKE) -f Makefile.coq

Makefile.coq: Makefile $(VS)
	coq_makefile -R $(ROOT)/src Bedrock \
		     $(VS) -o Makefile.coq

clean:: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq .depend
