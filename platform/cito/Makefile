BEDROCK := ../..

MODULES := \
	ValsStringSet SetUtil \
	Label ConvertLabel \
	SyntaxExpr Syntax SemanticsExpr FuncCore \
	ADT WordMap \
	Semantics \
	GeneralTactics \
	FreeVarsExpr Option Union FreeVars \
	RepInv Inv \
	DepthExpr Max Depth \
	WellFormed \
	CompileStmtSpec CompileExpr Notations CompileExprs SaveRet CompileStmtImpl \
	SetFacts SynReqFacts SemanticsFacts ListFacts WordFacts InvFacts FMapFacts2 \
	CompileStmtTactics \
	SepHints SepHintsUtil SepHints2 SepHints3 SepHints4 \
	LayoutHints LayoutHintsUtil LayoutHints2 LayoutHints3 \
	VerifCondOkTactics \
	VerifCondOkCall \
	SemanticsFacts3 SynReqFacts2 \
	PostOk \
	VerifCondOkNonCall \
	SynReqFacts3 \
	VerifCondOkNonCall2 \
	VerifCondOk \
	CompileStmt \
	SyntaxFunc SyntaxModule \
	CompileFuncSpec \
	SepHints5 \
	GetLocalVars GoodFunc GoodOptimizer SemanticsFacts2 StringSetFacts \
	CompileFuncImpl \
	CompileFunc \
	GoodFunction GoodModule \
	NameDecoration NameVC \
	CompileModule \
	NatFacts StringFacts \
	ListFacts2 \
	FMapFacts1 \
	StructuredModuleFacts \
	Stub \
	FSetFacts1 FMapFacts3 ConvertLabelMap \
	Stubs \
	# tests/Adder tests/AdderDriver tests/Recur tests/RecurDriver

VS      := $(MODULES:%=%.v)

.PHONY: coq clean
.PRECIOUS: tests/%.gen.ml tests/%.gen.s

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

LIB := $(BEDROCK)/platform/tests

tests/%.gen.ml: tests/%AMD64.v tests/%Driver.vo $(LIB)/ignoreFail.ml $(LIB)/printCode.ml Makefile
	cat $(LIB)/ignoreFail.ml >$@
	$(COQC) $< 2>/dev/null \
		| sed '/let coq_Unnamed_thm_/,/module/{/module/!d}' \
		| sed 's/   allWords_def/   fun _ -> []/' \
		| sed 's/   N.to_nat$$/   fun _ -> O/' \
		| sed 's/let rec nuke/type set = unit\n\nlet rec nuke/' \
		>>$@
	cat $(LIB)/printCode.ml >>$@

tests/%.gen.s: tests/%.gen.ml
	echo "	.data" >$@
	echo "	.global bedrock_heap" >>$@
	echo "bedrock_heap:" >>$@
	echo "	.fill 4*(1024*1024*25+50),1,0" >>$@
	echo >>$@
	echo "	.text" >>$@
	echo "	.global main_main" >>$@
	echo >>$@
	ocaml -w -x $< >>$@

%.exe: %.gen.o $(LIB)/sys.o $(LIB)/driver.o
	cc $^ -o $@
