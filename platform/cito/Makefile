BEDROCK := ../..

MODULES := \
	facade/Facade \
	# ListFacts1 ListFacts2 ListFacts3 \
	# SetoidListFacts \
	# FSetFacts1 \
	# FMapFacts1 FMapFacts2 \
	# StringSetFacts StringSetTactics \
	# StringMap StringMapFacts \
	# GLabel GLabelKey GLabelMap GLabelMapFacts \
	# LabelMapFacts \
	# WordKey WordMap WordMapFacts \
	# ConvertLabel \
	# ValsStringSet \
	# SyntaxExpr Syntax SemanticsExpr FuncCore \
	# ADT \
	# Semantics \
	# GeneralTactics \
	# FreeVarsExpr Option Union FreeVars \
	# RepInv Inv \
	# DepthExpr Max Depth \
	# WellFormed \
	# SynReqFactsUtil SynReqFacts SemanticsFacts ListFactsNew WordFacts InvFacts \
	# CompileStmtTactics \
	# SepHints SepHintsUtil SepHints2 SepHints3 SepHints4 \
	# LayoutHints LayoutHintsUtil LayoutHints2 LayoutHints3 \
	# SemanticsFacts3 SynReqFacts2 \
	# SynReqFacts3 \
	# SyntaxFunc SyntaxModule \
	# CompileFuncSpec \
	# SepHints5 \
	# GetLocalVars Wf GoodFunc GoodOptimizer SemanticsFacts2 \
	# CompileFuncImpl \
	# CompileFunc \
	# GoodFunction GoodModule \
	# NameDecoration NameVC \
	# CompileModule \
	# NatFacts StringFacts2 \
	# GeneralTactics2 \
	# StructuredModuleFacts \
	# ConvertLabelMap \
	# LinkSpec \
	# LinkModuleImpls \
	# Stub \
	# Stubs \
	# Link \
	# MakeADT MakeWrapper \
	# MaxFacts GetLocalVarsFacts \
	# IsGoodModule GoodModuleFacts GoodModuleDec \
	# LinkFacts \
	# GeneralTactics3 BedrockTactics Transit \
	# ProgramLogic ProgramLogic2 \
	# LinkSpecFacts \
	# Notations3 Notations4 \
	# WordFacts2 WordFacts3 WordFacts4 WordFacts5 \
	# SemanticsFacts4 ChangeSpec \

VS      := $(MODULES:%=%.v)

.PHONY: all light clean
.PRECIOUS: examples/%.gen.ml examples/%.gen.s

all: light
	$(MAKE) -f Makefile.compiler

light: Makefile.coq
	COQC='coqc' $(MAKE) -f Makefile.coq

COQARGS := -R $(BEDROCK)/src Bedrock \
	-R . Cito \
	-I $(BEDROCK)/platform
COQC    := coqc $(COQARGS)

Makefile.coq: Makefile $(VS)
	coq_makefile $(COQARGS) $(VS) -o Makefile.coq

clean:: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq .depend
	$(MAKE) -f Makefile.compiler clean

LIB := $(BEDROCK)/platform/tests

examples/%.gen.ml: examples/%AMD64.v examples/%Driver.vo $(LIB)/ignoreFail.ml $(LIB)/printCode.ml Makefile
	cat $(LIB)/ignoreFail.ml >$@
	$(COQC) $< 2>/dev/null \
		| sed '/let coq_Unnamed_thm_/,/module/{/module/!d}' \
		| sed 's/   allWords_def/   fun _ -> []/' \
		| sed 's/   N.to_nat$$/   fun _ -> O/' \
		| sed 's/let rec nuke/type set = unit\n\nlet rec nuke/' \
		>>$@
	cat $(LIB)/printCode.ml >>$@

examples/%.gen.s: examples/%.gen.ml
	echo "	.data" >$@
	echo "	.global bedrock_heap" >>$@
	echo "bedrock_heap:" >>$@
	echo "	.fill 4*(1024+50),1,0" >>$@
	echo >>$@
	echo "	.text" >>$@
	echo "	.global main_main" >>$@
	echo >>$@
	ocaml -w -x $< >>$@

%.exe: %.gen.o $(LIB)/sys.o $(LIB)/driver.o
	cc $^ -o $@
