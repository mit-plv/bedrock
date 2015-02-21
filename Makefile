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

HASNATDYNLINK = true

.DEFAULT_GOAL := examples

.PHONY: examples platform cito facade facade_all src src-test reification \
	install install-platform install-cito install-facade install-facade-all install-facade-allv install-src install-examples install-reification \
	selective-install selective-build \
	clean native ltac version dist time update-_CoqProject

Makefile.coq::
	$(VECHO) "COQ_MAKEFILE -f _CoqProject > $@"
	$(Q)$(COQBIN)coq_makefile COQC = "$(SILENCE_COQC)$(TIMER) \"\$$(COQBIN)coqc\"" COQDEP = "$(SILENCE_COQDEP)\"\$$(COQBIN)coqdep\" -c" -f _CoqProject > $@

Makefile.variables: Makefile.coq
	$(VECHO) "CAT $< | GREP > $@"
	$(Q)cat $< | grep -v '^%' | grep -v "^	" | grep -v '^\..*:.*' | grep -v '^-include' | grep -v '^[a-z-]*:\([^=]\|$$\)' > $@

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

dist:
	hg archive -t tgz /tmp/bedrock.tgz

ALL_EXAMPLES_V := $(filter Bedrock/Examples/%.v,$(VFILES))
EXAMPLES_V := $(addprefix Bedrock/Examples/,$(call not-containing,/,$(patsubst Bedrock/Examples/%,%,$(ALL_EXAMPLES_V))))
CITO_V := $(filter Bedrock/Platform/Cito/%.v,$(VFILES))
FACADE_ALLV := $(filter Bedrock/Platform/Facade/%.v,$(VFILES))
FACADE_V := \
	Bedrock/Facade/Facade.v \
	Bedrock/Facade/DFacade.v \
	Bedrock/Facade/CompileUnit.v

FACADE_ALL_V := \
	Bedrock/Facade/examples/FiatADTs.v \
	Bedrock/Facade/examples/FiatRepInv.v \
	Bedrock/Facade/examples/FiatImpl.v \
	Bedrock/Facade/DFacadeToBedrock.v

# Not sure why we have these files if no target refers to them...
PLATFORM_UNMADE_V := \
	Bedrock/Platform/tests/AbortAMD64.v \
	Bedrock/Platform/tests/ArrayTestAMD64.v \
	Bedrock/Platform/tests/CallbackAMD64.v \
	Bedrock/Platform/tests/ConnectAMD64.v \
	Bedrock/Platform/tests/Echo2AMD64.v \
	Bedrock/Platform/tests/Echo3AMD64.v \
	Bedrock/Platform/tests/EchoAMD64.v \
	Bedrock/Platform/tests/EchoServerAMD64.v \
	Bedrock/Platform/tests/ListBuilderAMD64.v \
	Bedrock/Platform/tests/MiniMasterAMD64.v \
	Bedrock/Platform/tests/MiniMasterI386.v \
	Bedrock/Platform/tests/PrintIntAMD64.v \
	Bedrock/Platform/tests/RosMasterAMD64.v \
	Bedrock/Platform/tests/RosMasterI386.v \
	Bedrock/Platform/tests/RtosAMD64.v \
	Bedrock/Platform/tests/RtosI386.v \
	Bedrock/Platform/tests/SharedListAMD64.v \
	Bedrock/Platform/tests/WebServerAMD64.v \
	Bedrock/Platform/tests/XmlTest2AMD64.v \
	Bedrock/Platform/tests/XmlTestAMD64.v

SRC_UNMADE_V := \
	Bedrock/ILTacLtac.v \
	Bedrock/ILTacML.v \
	Bedrock/SepExprTests.v \
	Bedrock/SymEvalTests.v \
	Bedrock/UnfolderTests.v \
	Bedrock/provers/TransitivityProver.v

PLATFORM_V := $(filter-out Bedrock/Platform/Facade/% Bedrock/Platform/Cito/% $(PLATFORM_UNMADE_V),$(filter Bedrock/Examples/%.v,$(VFILES)))

SRC_V := $(filter-out Bedrock/Platform/% Bedrock/Examples% $(SRC_UNMADE_V),$(VFILES))

SRC_TEST_V := \
	Bedrock/UnfolderTests.v

REIFICATION_V := \
	$(filter Bedrock/reification/%,$(VFILES)) $(CMOFILES) $(if $(HASNATDYNLINK_OR_EMPTY),$(CMXSFILES))

examples facade facade_all facade_allv cito platform src src-test: reification
install-examples examples: T = $(EXAMPLES_V)
install-facade facade: T = $(FACADE_V)
install-facade-all facade-all: T = $(FACADE_ALL_V)
install-facade-allv facade-allv: T = $(FACADE_ALLV)
install-cito cito: T = $(CITO_V)
install-platform platform: T = $(PLATFORM_V)
install-examples examples: T = $(EXAMPLES_V)
install-src src: T = $(SRC_V)

examples facade facade-all facade-allv cito platform src:
	$(Q)$(MAKE) -f Makefile.coq $(patsubst %.v,%.vo,$(T))

install-examples install-facade install-facade-all install-facade-allv install-cito install-platform install-src:
	$(VECHO) "MAKE -f Makefile.coq INSTALL"
	$(Q)$(MAKE) -f Makefile.coq VFILES="$(filter %.v,$(T))" install

reification:
	$(MAKE) -f Makefile.coq extlib.cmi
	$(MAKE) -f Makefile.coq $(patsubst %.v,%.vo,$(REIFICATION_V))

install:
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
