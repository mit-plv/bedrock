BEDROCK := ../..

MODULES := \
	StringSet ValsStringSet SetUtil \
	SyntaxExpr Syntax SemanticsExpr Semantics Safe \
	GeneralTactics SafeCoind \
	FreeVarsExpr Option Union FreeVars \
	Inv \
	DepthExpr Max Depth \
	CompileStmtSpec CompileExpr Notations CompileExprs CompileStmtImpl \
	SetFacts ScopeFacts SemanticsFacts ListFacts \
	CompileStmtTactics \
	PostOk \
	# VerifCondOk CompileStmt \
	# ExprLemmas VariableLemmas \
	# DepthExpr \
	# SemanticsExprLemmas SemanticsLemmas \
	# Depth SyntaxNotations \
	# CompileExpr SepLemmas \
	# GoodOptimizer PartialMap PartialMapSubtract ConstFolding ElimDead \
	# Compiler Wf WritingPrograms Compile Recall \
	# SetInterface SetNotations SetFunctors SetArrow SetList \
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
