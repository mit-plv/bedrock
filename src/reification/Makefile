PREFIX  := Bedrock.reification
MODULES := extlib.mli extlib.ml reif.ml4 example.v

.PHONY: coq clean install

coq: Makefile.coq
	$(MAKE) -f Makefile.coq extlib.cmi
	$(MAKE) -f Makefile.coq

Makefile.coq: Makefile $(MODULES)
	$(COQBIN)coq_makefile -R . $(PREFIX) \
		     $(MODULES) -o Makefile.coq

install: Makefile.coq
	$(MAKE) -f Makefile.coq install

clean:: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq .depend
