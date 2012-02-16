#SymEvalTests

MODULES    := HintlessOrderedType HintlessFMapList HintlessFMapAVL \
	Nomega Word IL LabelMap PropX PropXTac Memory \
	XCAP Structured StructuredModule Linker Programming \
	EqdepClass DepList Reflect \
	Heaps SepTheoryX \
	NatMap Expr ExprUnify \
	SepExpr SepExprTests \
	Provers \
	Unfolder UnfolderTests \
	Env \
	SymEval sep/PtsTo sep/Array \
	SepIL SepTac Bedrock
VS         := $(MODULES:%=%.v)

.PHONY: coq clean package

coq: Makefile.coq
	$(MAKE) -f Makefile.coq

Makefile.coq: Makefile $(VS)
	coq_makefile -R . Bedrock $(VS) -o Makefile.coq

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