PROVERS := Assumption Reflexivity Transitivity Word
MODULES    := HintlessOrderedType HintlessFMapInterface \
	HintlessFMapList HintlessFMapAVL HintlessFMapFacts \
	Reflection \
	GenRec Ordering Multimap Folds \
	Nomega Word Labels LabelMap \
	PropX PropXRel PropXTac \
	Memory \
	XCAP Structured StructuredModule Linker Programming \
	EqdepClass Decidables DepList Reflect \
	Heaps SepTheoryX SepTheoryXIL \
	NatMap Expr ExprUnify \
	Prover Provers \
	$(PROVERS:%=provers/%Prover) \
	SepExpr SepHeap SepUnify SepCancel \
	Unfolder \
	Env TypedPackage \
	SymEval sep/PtsTo sep/Array \
	IL \
	ILEnv SepIL \
	SymIL SymILProofs SymILTac \
	ILTac \
	Bedrock
TESTS := UnfolderTests
VS         := $(MODULES:%=%.v)
TVS        := $(TESTS:%=%.v)
ARGS :=-R . Bedrock

.PHONY: coq clean package

coq: Makefile.coq
	$(MAKE) -f Makefile.coq

Makefile.coq: Makefile $(VS)
	coq_makefile $(ARGS) $(VS) -o Makefile.coq

Makefile.test.coq: Makefile $(TVS)
	coq_makefile $(ARGS) $(TVS) -o Makefile.test.coq

test: coq Makefile.test.coq
	$(MAKE) -f Makefile.test.coq

clean:: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq .depend

package:
	hg archive -t tgz /tmp/bedrock.tgz

admit:
	@ grep -e 'admit' -e 'Admitted' ${VS}

depgraph: Makefile.coq
	@ echo Generating dependency graph to ../deps.pdf
	@ ./../tools/deps.py $(MODULES:%=%.v.d) > ../deps.dot
	@ ./../tools/deps.py $(MODULES:%=%.v.d) | dot -Tpdf -o ../deps.pdf

toplevel: coq
	coqtop.opt $(ARGS)