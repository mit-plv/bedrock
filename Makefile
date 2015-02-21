V = 0

SILENCE_COQC_0 := @echo \"COQC $$<\"; #
SILENCE_COQC_1 :=
SILENCE_COQC = $(SILENCE_COQC_$(V))

SILENCE_COQDEP_0 := @echo \"COQDEP $$<\"; #
SILENCE_COQDEP_1 :=
SILENCE_COQDEP = $(SILENCE_COQDEP_$(V))

Q_0 := @
Q_1 :=
Q = $(Q_$(V))

VECHO_0 := @echo
VECHO_1 := @true
VECHO = $(VECHO_$(V))

TIMED=
TIMECMD=
STDTIME?=/usr/bin/time -f \"$$* (user: %U mem: %M ko)\"
TIMER=$(if $(TIMED), $(STDTIME), $(TIMECMD))

containing = $(foreach v,$2,$(if $(findstring $1,$v),$v))
not-containing = $(foreach v,$2,$(if $(findstring $1,$v),,$v))

.DEFAULT_GOAL := examples

.PHONY: examples platform cito facade facade_all src clean native ltac version dist time install install-platform install-cito install-facade install-facade-all install-facade-allv install-src install-examples update-_CoqProject

Makefile.coq::
	$(VECHO) "COQ_MAKEFILE -f _CoqProject > $@"
	$(Q)$(COQBIN)coq_makefile COQC = "$(SILENCE_COQC)$(TIMER) \"\$$(COQBIN)coqc\"" COQDEP = "$(SILENCE_COQDEP)\"\$$(COQBIN)coqdep\" -c" -f _CoqProject > $@

Makefile.variables: Makefile.coq
	$(VECHO) "CAT $< | GREP > $@"
	$(Q)cat $< | grep -v '^%' | grep -v "^	" | grep -v '\..*:.*' | grep -v '^-include' | grep -v '^[a-z-]*:\([^=]\|$$\)' | grep -v '^COQC' > $@

-include Makefile.variables

clean::
	$(VECHO) "RM *.CMO *.CMI *.CMA"
	$(Q)rm -f $(ALLCMOFILES) $(CMIFILES) $(CMAFILES)
	$(VECHO) "RM *.CMX *.CMXS *.CMXA *.O *.A"
	$(Q)rm -f $(ALLCMOFILES:.cmo=.cmx) $(CMXAFILES) $(CMXSFILES) $(ALLCMOFILES:.cmo=.o) $(CMXAFILES:.cmxa=.a)
	$(VECHO) "RM *.ML.D *.MLI.D *.ML4.D *.MLLIB.D"
	$(Q)rm -f $(addsuffix .d,$(MLFILES) $(MLIFILES) $(ML4FILES) $(MLLIBFILES) $(MLPACKFILES))
	$(VECHO) "RM *.VO *.VI *.G *.V.D *.V.BEAUTIFIED *.V.OLD"
	$(Q)rm -f $(VOFILES) $(VIFILES) $(GFILES) $(VFILES:.v=.v.d) $(VFILES:=.beautified) $(VFILES:=.old)
	$(VECHO) "RM *.PS *.PDF *.GLOB *.TEX *.G.TEX"
	$(Q)rm -f all.ps all-gal.ps all.pdf all-gal.pdf all.glob $(VFILES:.v=.glob) $(VFILES:.v=.tex) $(VFILES:.v=.g.tex) all-mli.tex
	- rm -rf html mlihtml
	rm -f Makefile.coq Makefile.variables .depend

native:
	$(MAKE) -C Bedrock native

ltac:
	$(MAKE) -C Bedrock ltac

version:
	$(MAKE) -C Bedrock version

dist:
	hg archive -t tgz /tmp/bedrock.tgz

ALL_EXAMPLES_VO := $(filter Bedrock/Examples/%.vo,$(VOFILES))
EXAMPLES_VO := $(addprefix Bedrock/Examples/,$(call not-containing,/,$(patsubst Bedrock/Examples/%,%,$(ALL_EXAMPLES_VO))))
CITO_VO := $(filter Bedrock/Platform/Cito/%.vo,$(VOFILES))
FACADE_ALLVO := $(filter Bedrock/Platform/Facade/%.vo,$(VOFILES))
FACADE_VO := \
	Bedrock/Facade/Facade.vo \
	Bedrock/Facade/DFacade.vo \
	Bedrock/Facade/CompileUnit.vo

FACADE_ALL_VO := \
	Bedrock/Facade/examples/FiatADTs.vo \
	Bedrock/Facade/examples/FiatRepInv.vo \
	Bedrock/Facade/examples/FiatImpl.vo \
	Bedrock/Facade/DFacadeToBedrock.vo

# Not sure why we have these files if no target refers to them...
PLATFORM_UNMADE_VO := \
	Bedrock/Platform/tests/AbortAMD64.vo \
	Bedrock/Platform/tests/ArrayTestAMD64.vo \
	Bedrock/Platform/tests/CallbackAMD64.vo \
	Bedrock/Platform/tests/ConnectAMD64.vo \
	Bedrock/Platform/tests/Echo2AMD64.vo \
	Bedrock/Platform/tests/Echo3AMD64.vo \
	Bedrock/Platform/tests/EchoAMD64.vo \
	Bedrock/Platform/tests/EchoServerAMD64.vo \
	Bedrock/Platform/tests/ListBuilderAMD64.vo \
	Bedrock/Platform/tests/MiniMasterAMD64.vo \
	Bedrock/Platform/tests/MiniMasterI386.vo \
	Bedrock/Platform/tests/PrintIntAMD64.vo \
	Bedrock/Platform/tests/RosMasterAMD64.vo \
	Bedrock/Platform/tests/RosMasterI386.vo \
	Bedrock/Platform/tests/RtosAMD64.vo \
	Bedrock/Platform/tests/RtosI386.vo \
	Bedrock/Platform/tests/SharedListAMD64.vo \
	Bedrock/Platform/tests/WebServerAMD64.vo \
	Bedrock/Platform/tests/XmlTest2AMD64.vo \
	Bedrock/Platform/tests/XmlTestAMD64.vo

SRC_UNMADE_VO := \
	Bedrock/ILTacLtac.vo \
	Bedrock/ILTacML.vo \
	Bedrock/SepExprTests.vo \
	Bedrock/SymEvalTests.vo \
	Bedrock/UnfolderTests.vo \
	Bedrock/provers/TransitivityProver.vo

PLATFORM_VO := $(filter-out Bedrock/Platform/Facade/% Bedrock/Platform/Cito/% $(PLATFORM_UNMADE_VO),$(filter Bedrock/Examples/%.vo,$(VOFILES)))

SRC_VO := $(filter-out Bedrock/Platform/% Bedrock/Examples% $(SRC_UNMADE_VO),$(VOFILES))

SRC_TEST_VO := \
	Bedrock/UnfolderTests.vo

examples: src
	$(MAKE) -f Makefile.coq $(EXAMPLES_VO)

facade: src
	$(MAKE) -f Makefile.coq $(FACADE_VO)

facade_all: src
	$(MAKE) -f Makefile.coq $(FACADE_ALL_VO)

facade_allv: src
	$(MAKE) -f Makefile.coq $(FACADE_ALLVO)

cito: src
	$(MAKE) -f Makefile.coq $(CITO_VO)

platform: src
	$(MAKE) -f Makefile.coq $(PLATFORM_VO)

src:
	$(MAKE) -C Bedrock/reification
	$(MAKE) -f Makefile.coq $(SRC_VO)

src-test:
	$(MAKE) -f Makefile.coq $(SRC_TEST_VO)

install-examples: T=$(EXAMPLES_VO)
install-examples: selective-install
install-facade: T=$(FACADE_VO)
install-facade: selective-install
install-facade-all: T=$(FACADE_ALL_VO)
install-facade-all: selective-install
install-facade-allv: T=$(FACADE_ALLVO)
install-facade-allv: selective-install
install-cito: T=$(CITO_VO)
install-cito: selective-install
install-platform: T=$(PLATFORM_VO)
install-platform: selective-install
install-examples: T=$(EXAMPLES_VO)
install-examples: selective-install
install-examples: T=$(EXAMPLES_VO)
install-examples: selective-install

# TODO: combine Bedrock/reification/Makefile with this makefile
install-src: T=$(SRC_VO)
install-src: selective-install
	$(MAKE) -C Bedrock/reification install

selective-install:
	cd "." && for i in $(addsuffix .vo,$(basename $(T))) $(addsuffix .v,$(basename $(T))) $(addsuffix .glob,$(basename $(T))); do \
	 install -d "`dirname "$(DSTROOT)"$(COQLIBINSTALL)/Bedrock/$$i`"; \
	 install -m 0644 $$i "$(DSTROOT)"$(COQLIBINSTALL)/Bedrock/$$i; \
	done

install:
	$(MAKE) -C Bedrock/reification install
	$(MAKE) -f Makefile.coq install

update-_CoqProject:
	(echo '-R Bedrock Bedrock'; echo '-I Bedrock/reification'; find Bedrock -name "*.v"; find Bedrock/reification -name "*.mli" -o -name "*.ml4" -o -name "*.ml") > _CoqProject

time:
	@ rm -rf timing
	@ ./tools/timer.py timing/ $(shell find Bedrock -name "*.v")
	@ cp Makefile timing/Makefile
	@ cp -r Bedrock/Makefile Bedrock/Makefile.coq Bedrock/reification/ timing/Bedrock
	@ cp Bedrock/Examples/Makefile Bedrock/Examples/Makefile.coq timing/Bedrock/Examples
	@ (cd timing; $(MAKE) all)

native:
	@ echo "## "
	@ echo "## Switching to OCaml reification."
	@ echo "## "
	$(Q) (cd Bedrock/; rm -f ILTac.v ILTac.vo ILTac.v.d ILTac.glob)
	$(Q) (cd Bedrock/; ln -s ILTacML.v ILTac.v)
	$(Q) $(MAKE) -C Bedrock/reification

ltac:
	@ echo "## "
	@ echo "## Switching to ltac reification."
	@ echo "## "
	$(Q) (cd Bedrock/; rm -f ILTac.v ILTac.vo ILTac.v.d ILTac.glob)
	$(Q) (cd Bedrock/; ln -s ILTacLtac.v ILTac.v)

Bedrock/ILTac.v:
	@ echo "## "
	@ echo "## Warning: No ILTac.v, defaulting to Ltac reification."
	@ echo "## NOTE: If you would like to use the faster, ML reification"
	@ echo "##       run 'make native'"
	@ echo "## "
	$(Q) $(MAKE) native

version:
	@ echo "## "
	@ echo "## You are running" $(patsubst Bedrock/ILTac%.v,%,$(shell readlink Bedrock/ILTac.v)) "reification"
	@ echo "## "

package:
	hg archive -t tgz /tmp/bedrock.tgz

admit:
	$(Q) grep -n -e 'admit' -e 'Admitted' $(VFILES)

depgraph:
	@ echo Generating dependency graph to deps.pdf
	$(VECHO) "DEPS.PY *.V.D > DEPS.DOT"
	$(Q) ./tools/deps.py $(SRC_VOFILES:%.v=%.v.d) > deps.dot
	$(VECHO) "DEPS.PY *.V.D | DOT -o DEPS.PDF"
	$(Q) ./tools/deps.py $(SRC_VOFILES:%.v=%.v.d) | dot -Tpdf -o deps.pdf
