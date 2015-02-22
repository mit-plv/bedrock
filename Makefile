V = 0

SILENCE_COQC_0 = @echo "COQC $<"; #
SILENCE_COQC_1 =
SILENCE_COQC = $(SILENCE_COQC_$(V))

SILENCE_COQDEP_0 = @echo "COQDEP $<"; #
SILENCE_COQDEP_1 =
SILENCE_COQDEP = $(SILENCE_COQDEP_$(V))

SILENCE_OCAMLC_0 = @echo "OCAMLC $<"; #
SILENCE_OCAMLC_1 =
SILENCE_OCAMLC = $(SILENCE_OCAMLC_$(V))

SILENCE_OCAMLDEP_0 = @echo "OCAMLDEP $<"; #
SILENCE_OCAMLDEP_1 =
SILENCE_OCAMLDEP = $(SILENCE_OCAMLDEP_$(V))

SILENCE_OCAMLOPT_0 = @echo "OCAMLOPT $<"; #
SILENCE_OCAMLOPT_1 =
SILENCE_OCAMLOPT = $(SILENCE_OCAMLOPT_$(V))

Q_0 := @
Q_1 :=
Q = $(Q_$(V))

VECHO_0 := @echo
VECHO_1 := @true
VECHO = $(VECHO_$(V))

TIMED=
TIMECMD=
STDTIME?=/usr/bin/time -f "$* (real: %e, user: %U, sys: %S, mem: %M ko)"
TIMER=$(if $(TIMED), $(STDTIME), $(TIMECMD))

containing = $(foreach v,$2,$(if $(findstring $1,$v),$v))
not-containing = $(foreach v,$2,$(if $(findstring $1,$v),,$v))

HASNATDYNLINK = true

.DEFAULT_GOAL := examples

.PHONY: examples platform cito facade facade_all src src-test reification \
	install install-platform install-cito install-facade install-facade-all install-facade-allv install-src install-examples install-reification \
	selective-install selective-build \
	clean native ltac version dist time update-_CoqProject

FAST_TARGETS := clean archclean printenv dist version package admit clean-old update-_CoqProject time native ltac

# pipe the output of coq_makefile through sed so that we don't have to run coqdep just to clean
Makefile.coq: Makefile _CoqProject
	$(VECHO) "COQ_MAKEFILE -f _CoqProject > $@"
	$(Q)$(COQBIN)coq_makefile COQC = "\$$(SILENCE_COQC)\$$(TIMER) \"\$$(COQBIN)coqc\"" COQDEP = "\$$(SILENCE_COQDEP)\"\$$(COQBIN)coqdep\" -c" -f _CoqProject | sed s'/^\(-include.*\)$$/ifneq ($$(filter-out $(FAST_TARGETS),$$(MAKECMDGOALS)),)\n\1\nelse\nifeq ($$(MAKECMDGOALS),)\n\1\nendif\nendif/g' | sed s'/^clean:$$/clean-old::/g' > $@

-include Makefile.coq

# overwrite OCAMLC, OCAMLOPT, OCAMLDEP to make `make` quieter
OCAMLC_OLD := $(OCAMLC)
OCAMLC = $(SILENCE_OCAMLC)$(OCAMLC_OLD)

OCAMLDEP_OLD := $(OCAMLDEP)
OCAMLDEP = $(SILENCE_OCAMLDEP)$(OCAMLDEP_OLD)

OCAMLOPT_OLD := $(OCAMLOPT)
OCAMLOPT = $(SILENCE_OCAMLOPT)$(OCAMLOPT_OLD)

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
	rm -f Bedrock/ILTac.v Bedrock/reification/extlib.cmi
	rm -f Makefile.coq .depend

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

REIFICATION_VO := \
	$(filter Bedrock/reification/%,$(VOFILES)) $(CMOFILES) $(if $(HASNATDYNLINK_OR_EMPTY),$(CMXSFILES))

examples facade facade-all facade-allv cito platform src src-test: reification
examples: $(EXAMPLES_VO)
facade: $(FACADE_VO)
facade-all: $(FACADE_ALL_VO)
facade-allv: $(FACADE_ALLVO)
cito: $(CITO_VO)
platform: $(PLATFORM_VO)
src: $(SRC_VO)
src-test: $(SRC_TEST_VO)


install-examples: T = $(EXAMPLES_VO)
install-facade: T = $(FACADE_VO)
install-facade-all: T = $(FACADE_ALL_VO)
install-facade-allv: T = $(FACADE_ALLVO)
install-cito: T = $(CITO_VO)
install-platform: T = $(PLATFORM_VO)
install-examples: T = $(EXAMPLES_VO)
install-src: T = $(SRC_VO)

examples facade facade-all facade-allv cito platform src:
	$(Q)$(MAKE) -f Makefile.coq $(patsubst %.v,%.vo,$(T))

install-examples install-facade install-facade-all install-facade-allv install-cito install-platform install-src:
	$(VECHO) "MAKE -f Makefile.coq INSTALL"
	$(Q)$(MAKE) -f Makefile.coq VFILES="$(addsuffix .v,$(basename $(filter %.vo,$(T))))" install

reification: Bedrock/reification/extlib.cmi $(REIFICATION_VO)

update-_CoqProject:
	(echo '-R Bedrock Bedrock'; echo '-I Bedrock/reification'; find Bedrock -name "*.v" -a ! -wholename 'Bedrock/ILTac.v'; echo 'Bedrock/ILTac.v'; find Bedrock/reification -name "*.mli" -o -name "*.ml4" -o -name "*.ml") > _CoqProject

time:
	@ rm -rf timing
	@ ./tools/timer.py timing/ $(shell find Bedrock -name "*.v")
	@ cp Makefile timing/Makefile
	@ cp -r Bedrock/Makefile Bedrock/Makefile.coq Bedrock/reification/ timing/Bedrock
	@ cp Bedrock/Examples/Makefile Bedrock/Examples/Makefile.coq timing/Bedrock/Examples
	@ (cd timing; $(MAKE) all)

REIF_VERSION = $(patsubst ILTac%.v,%,$(shell readlink Bedrock/ILTac.v))

ifeq ($(REIF_VERSION),ML)
native: reification
else
native:
	@ echo "## "
	@ echo "## Switching to OCaml reification."
	@ echo "## "
	$(Q) (cd Bedrock/; rm -f ILTac.v ILTac.vo ILTac.v.d ILTac.glob)
	$(Q) (cd Bedrock/; ln -s ILTacML.v ILTac.v)
	$(Q) $(MAKE) reification
endif

ifeq ($(REIF_VERSION),Ltac)
ltac:
else
ltac:
	@ echo "## "
	@ echo "## Switching to Ltac reification."
	@ echo "## "
	$(Q) (cd Bedrock/; rm -f ILTac.v ILTac.vo ILTac.v.d ILTac.glob)
	$(Q) (cd Bedrock/; ln -s ILTacLtac.v ILTac.v)
endif

Bedrock/ILTac.v:
	@ echo "## "
	@ echo "## Warning: No ILTac.v, defaulting to ML reification."
	@ echo "## "
	$(Q) $(MAKE) native

version:
	@ echo "## "
	@ echo "## You are running $(REIF_VERSION) reification"
	@ echo "## "

package:
	hg archive -t tgz /tmp/bedrock.tgz

admit:
	$(Q) grep -n -e 'admit' -e 'Admitted' $(VFILES)

depgraph:
	@ echo Generating dependency graph to deps.pdf
	$(VECHO) "DEPS.PY *.V.D > DEPS.DOT"
	$(Q) ./tools/deps.py $(SRC_VO:%.vo=%.v.d) > deps.dot
	$(VECHO) "DEPS.PY *.V.D | DOT -o DEPS.PDF"
	$(Q) ./tools/deps.py $(SRC_VO:%.vo=%.v.d) | dot -Tpdf -o deps.pdf
