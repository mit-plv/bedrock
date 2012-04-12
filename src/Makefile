#SymEvalTests

MODULES    := HintlessOrderedType HintlessFMapList HintlessFMapAVL \
	Nomega Word IL LabelMap \
	PropX PropXRel PropXTac \
	Memory \
	XCAP Structured StructuredModule Linker Programming \
	EqdepClass Decidables DepList Reflect \
	Heaps SepTheoryX \
	NatMap Expr ExprUnify ExprUnify2 \
	Prover Provers \
	SepExpr \
	Unfolder \
	Env TypedPackage \
	SymEval sep/PtsTo \
	ILEnv SepIL SymIL ILTac \
	Bedrock
VS         := $(MODULES:%=%.v)
ARGS :=-R . Bedrock

#SepExprTests UnfolderTests 

.PHONY: coq clean package

coq: Makefile.coq
	$(MAKE) -f Makefile.coq

Makefile.coq: Makefile $(VS)
	coq_makefile $(ARGS) $(VS) -o Makefile.coq

clean:: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq .depend

package:
	hg archive -t tgz /tmp/bedrock.tgz

admit:
	@ echo Admitted lemmas --------------------------
	@ grep admit *.v
	@ grep Admitted *.v

depgraph: Makefile.coq
	@ echo Generating dependency graph to ../deps.pdf
	@ ./../tools/deps.py $(MODULES:%=%.v.d) | dot -Tpdf -o ../deps.pdf

toplevel: coq
	coqtop.opt $(ARGS)