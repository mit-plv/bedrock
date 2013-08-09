BEDROCK := ../..

MODULES := GeneralTactics ExprLemmas VariableLemmas SyntaxExpr SemanticsExpr \
	DepthExpr FootprintExpr \
	SemanticsExprLemmas Syntax Dict Semantics Footprint SemanticsLemmas \
	CompileExpr MyMalloc MyFree SepLemmas CompileStatement \
	Compiler Wf WritingPrograms Compile Recall \
	tests/Adder tests/AdderDriver tests/Recur tests/RecurDriver

VS      := $(MODULES:%=%.v)

.PHONY: coq clean

coq: Makefile.coq
	COQC='time coqc -verbose' $(MAKE) -f Makefile.coq

COQARGS := -R $(BEDROCK)/src Bedrock \
	-R . Cito \
	-I $(BEDROCK)/platform \
	-I tests
COQC    := coqc $(COQARGS)

Makefile.coq: Makefile $(VS)
	coq_makefile $(COQARGS) $(VS) -o Makefile.coq

clean:: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq .depend

%.gen.s: %AMD64.v %Driver.vo
	echo "	.data" >$@
	echo "	.global bedrock_heap" >>$@
	echo "bedrock_heap:" >>$@
	echo "	.fill 4*(1024*1024*25+50),1,0" >>$@
	echo >>$@
	echo "	.text" >>$@
	echo "	.global main_main" >>$@
	echo >>$@
	$(COQC) $< \
		| sed 's/^.*:: nil//' \
		| sed 's/^.*:: *//' \
		| sed 's/^.*: list string//' \
		| sed 's/^.*= "//' \
		| sed 's/^.*"//' \
		>>$@

%.exe: %.gen.o $(BEDROCK)/platform/tests/sys.o $(BEDROCK)/platform/tests/driver.o
	cc $^ -o $@
