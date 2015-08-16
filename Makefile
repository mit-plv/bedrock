STDTIME?=time -f "$* (real: %e, user: %U, sys: %S, mem: %M ko)"

.PHONY: examples platform cito facade facade-all facade-allv src reification \
	install install-platform install-cito install-facade install-facade-all install-facade-allv install-src install-examples install-reification \
	native ltac version dist time

.DEFAULT_GOAL := examples

submodule-update: .gitmodules
	git submodule update --init && \
	touch "$@"

ifneq (,$(wildcard .git)) # if we're in a git repo
etc/coq-scripts/Makefile.coq.common: submodule-update
	@ touch "$@"
endif

HASNATDYNLINK = true

FAST_TARGETS += dist version package admit etc/coq-scripts etc/coq-scripts/Makefile.coq.common submodule-update time native ltac
SUPER_FAST_TARGETS += submodule-update

Makefile.coq: etc/coq-scripts/Makefile.coq.common

-include etc/coq-scripts/Makefile.coq.common

clean::
	rm -f Bedrock/ILTac.v Bedrock/reification/extlib.cmi

dist:
	hg archive -t tgz /tmp/bedrock.tgz

ALL_EXAMPLES_VO := $(filter Bedrock/Examples/%.vo,$(VOFILES))
EXAMPLES_VO := $(addprefix Bedrock/Examples/,$(call not-containing,/,$(patsubst Bedrock/Examples/%,%,$(ALL_EXAMPLES_VO))))
CITO_VO := $(filter Bedrock/Platform/Cito/%.vo,$(VOFILES))
FACADE_ALLVO := $(filter Bedrock/Platform/Facade/%.vo,$(VOFILES))
FACADE_VO := \
	Bedrock/Platform/Facade/Facade.vo \
	Bedrock/Platform/Facade/DFacade.vo \
	Bedrock/Platform/Facade/CompileUnit.vo

FACADE_ALL_VO := \
	Bedrock/Platform/Facade/examples/FiatADTs.vo \
	Bedrock/Platform/Facade/examples/FiatRepInv.vo \
	Bedrock/Platform/Facade/examples/FiatImpl.vo \
	Bedrock/Platform/Facade/DFacadeToBedrock.vo \
	Bedrock/Platform/Facade/DFacadeToBedrock2.vo \

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
	Bedrock/provers/TransitivityProver.vo

PLATFORM_VO := $(filter-out Bedrock/Platform/Facade/% Bedrock/Platform/Cito/% $(PLATFORM_UNMADE_VO),$(filter Bedrock/Platform/%.vo,$(VOFILES)))

SRC_VO := $(filter-out Bedrock/Platform/% Bedrock/Examples% $(SRC_UNMADE_VO),$(VOFILES))

REIFICATION_VO := \
	$(filter Bedrock/reification/%,$(VOFILES)) $(CMOFILES) $(if $(HASNATDYNLINK_OR_EMPTY),$(CMXSFILES))

examples facade facade-all facade-allv cito platform src: reification
examples: $(EXAMPLES_VO)
facade: $(FACADE_VO)
facade-all: $(FACADE_ALL_VO)
facade-allv: $(FACADE_ALLVO)
cito: $(CITO_VO)
platform: $(PLATFORM_VO)
src: $(SRC_VO)


install-examples: T = $(EXAMPLES_VO)
install-facade: T = $(FACADE_VO)
install-facade-all: T = $(FACADE_ALL_VO)
install-facade-allv: T = $(FACADE_ALLVO)
install-cito: T = $(CITO_VO)
install-platform: T = $(PLATFORM_VO)
install-examples: T = $(EXAMPLES_VO)
install-src: T = $(SRC_VO)

install-examples install-facade install-facade-all install-facade-allv install-cito install-platform install-src:
	$(VECHO) "MAKE -f Makefile.coq INSTALL"
	$(Q)$(MAKE) -f Makefile.coq VFILES="$(call vo_to_installv,$(T))" install

reification: Bedrock/reification/extlib.cmi $(REIFICATION_VO)

SORT_COQPROJECT = sed 's,[^/]*/,~&,g' | env LC_COLLATE=C sort | sed 's,~,,g'

$(UPDATE_COQPROJECT_TARGET):
	(echo '-R Bedrock Bedrock'; echo '-I Bedrock/reification'; find Bedrock -name "*.v" -a ! -wholename 'Bedrock/ILTac.v' | $(SORT_COQPROJECT); echo 'Bedrock/ILTac.v'; find Bedrock/reification -name "*.mli" -o -name "*.ml4" -o -name "*.ml" | $(SORT_COQPROJECT)) > _CoqProject

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

$(VFILES:.v=.v.d): | Bedrock/ILTac.v

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
