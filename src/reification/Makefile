ROOT    := ../..
MODULES := extlib.mli extlib.ml reif.ml4 example.v

.PHONY: coq clean

coq: Makefile.coq
	$(MAKE) -f Makefile.coq extlib.cmi
	$(MAKE) -f Makefile.coq

Makefile.coq: Makefile $(MODULES)
	$(COQBIN)coq_makefile -R $(ROOT)/src Bedrock \
		     $(MODULES) -o Makefile.coq

clean:: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq .depend
