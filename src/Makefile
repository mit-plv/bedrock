MODULES    := OrderedType FMapList FMapAVL \
	Nomega Word IL LabelMap PropX PropXTac \
	XCAP Structured StructuredModule Linker Programming \
	EqdepClass Env PMap Reflect \
	Heaps SepTheoryX \
	dep/Expr dep/ExprUnify dep/SepExpr dep/SepExprTests dep/Provers \
	ndep/Expr \
	SepIL Bedrock
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
