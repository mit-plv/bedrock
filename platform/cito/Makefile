BEDROCK := ../..

ALL := $(basename $(shell find . -name \*.v))

EXAMPLES := $(basename $(shell find examples -name \*.v))

FACADE := \
	facade/Facade \

.PHONY: default all examples facade build clean
.PRECIOUS: examples/%.gen.ml examples/%.gen.s

default: all

all: T=$(ALL)
all: build

examples: T=$(EXAMPLES)
examples: build

facade: T=$(FACADE)
facade: build

build:  
	coq_makefile $(COQARGS) $(T:=.v) -o Makefile.coq
	echo '-include $(addsuffix .d,$(shell find . -name \*.v))' >> Makefile.coq
	COQC='coqc' $(MAKE) -f Makefile.coq

COQARGS := -R $(BEDROCK)/src Bedrock \
	-R . Cito \
	-I $(BEDROCK)/platform
COQC    := coqc $(COQARGS)

clean:: 
	rm -f Makefile.coq .depend
	rm -f *.v.d
	rm -f *.vo
	rm -f *.glob

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
