#DEP := PMap Expr ExprUnify SepExpr SepExprTests Provers
DEP  := 
NDEP := NatMap Expr ExprUnify \
	SepExpr SepExprTests \
	Provers \
	Unfolder UnfolderTests \
	SymEval 
#SymEvalTests

MODULES    := OrderedType FMapList FMapAVL \
	Nomega Word IL LabelMap PropX PropXTac Memory \
	XCAP Structured StructuredModule Linker Programming \
	EqdepClass DepList Reflect \
	Heaps SepTheoryX \
	$(DEP:%=dep/%) $(NDEP:%=ndep/%) \
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
