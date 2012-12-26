ROOT    := ..
MODULES := AutoSepExt PreAutoSep \
           Util \
           AutoSep \
           Malloc \
           Bags Queue Scheduler Thread \
           Bootstrap \
           tests/LinkTest tests/BabyThread tests/BabyThreadDriver

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
