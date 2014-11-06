ROOT    := ..

MODULES := Conditional AutoSepExt PreAutoSep \
	   Wrap \
           Util \
           AutoSep Misc \
           Sys Safety \
           Malloc \
           Bags Sets Queue ThreadQueue ThreadQueues SinglyLinkedList ListSegment Scheduler Thread \
           Bootstrap Arrays8 MoreArrays \
           tests/Thread0 \
           tests/LinkTest tests/Abort tests/PrintInt tests/ArrayTest tests/Echo tests/Echo2 \
           tests/AbortDriver tests/PrintIntDriver tests/ArrayTestDriver tests/EchoDriver tests/Echo2Driver \
           tests/BabyThread tests/Yield tests/Spawn tests/ListBuilder tests/SharedList tests/Echo3 tests/Connect \
           Buffers Io tests/StringDb tests/EchoServer tests/WebServer \
           tests/BabyThreadDriver tests/ListBuilderDriver tests/SharedListDriver tests/Echo3Driver tests/ConnectDriver \
           tests/WebServerDriver tests/EchoServerDriver \
           NumOps ArrayOps StringOps RelDb RelDbCondition RelDbSelect RelDbInsert RelDbDelete \
           XmlLex XmlSearch XmlOutput XmlLang Http HttpQ XmlProg Xml \
	   tests/XmlTestDriver tests/XmlTest2Driver tests/CallbackDriver \
           tests/Ros tests/MiniMasterDriver tests/RosMasterDriver

VNAME := -name \*.v ! -name \*.#\*

CITO := $(shell find cito $(VNAME))

FACADE := \
	facade/Facade \
	facade/FacadeADTs \

FACADE_ALL := $(shell find facade $(VNAME))

.PHONY: default platform cito facade build clean master
.PRECIOUS: tests/%.gen.ml tests/%.gen.s

default: platform

platform: T=$(MODULES)
platform: build

cito: T=$(CITO)
cito: build

facade: T=$(FACADE)
facade: build

facade_all: T=$(FACADE_ALL)
facade_all: build

COQARGS := -R $(ROOT)/src Bedrock -I . -I tests -R cito Cito -R facade Facade

COQC    := coqc $(COQARGS)

build:  
	coq_makefile $(COQARGS) $(addsuffix .v,$(basename $(T))) -o Makefile.coq
	echo '-include $(addsuffix .d,$(shell find . -name \*.v ! -name \*.#\*))' >> Makefile.coq
	$(MAKE) -f Makefile.coq

clean: 
	rm -f Makefile.coq .depend
	./rmr .v.d
	./rmr .vo
	./rmr .glob

tests/%.gen.ml: tests/%AMD64.v tests/%Driver.vo tests/ignoreFail.ml tests/printCode.ml Makefile
	cat tests/ignoreFail.ml >$@
	$(COQC) $< 2>/dev/null \
		| sed '/let coq_Unnamed_thm_/,/module/{/module/!d}' \
		| sed 's/   allWords_def/   fun _ -> []/' \
		| sed 's/   N.to_nat$$/   fun _ -> O/' \
		>>$@
	cat tests/printCode.ml >>$@

tests/%.gen.s: tests/%.gen.ml tests/%.txt
	echo "	.data" >$@
	echo "	.global bedrock_heap" >>$@
	echo "bedrock_heap:" >>$@
	echo "	.fill 4*(1024*1024*200+50+`cat tests/$*.txt`),1,0" >>$@
	echo >>$@
	echo "	.text" >>$@
	echo "	.global main_main" >>$@
	echo >>$@
	ocaml -w -x $< >>$@

tests/%32.gen.ml: tests/%I386.v tests/%Driver.vo tests/ignoreFail.ml tests/printCode.ml Makefile
	cat tests/ignoreFail.ml >$@
	$(COQC) $< 2>/dev/null \
		| sed '/let coq_Unnamed_thm_/,/module/{/module/!d}' \
		| sed 's/   allWords_def/   fun _ -> []/' \
		| sed 's/   N.to_nat$$/   fun _ -> O/' \
		>>$@
	cat tests/printCode.ml >>$@

tests/%32.gen.s: tests/%32.gen.ml tests/%.txt
	echo "	.data" >$@
	echo "	.global bedrock_heap" >>$@
	echo "bedrock_heap:" >>$@
	echo "	.fill 4*(1024*1024*200+50+`cat tests/$*.txt`),1,0" >>$@
	echo >>$@
	echo "	.text" >>$@
	echo "	.global main_main" >>$@
	echo >>$@
	ocaml -w -x $< >>$@

tests/%.exe: tests/%.gen.o tests/sys.o tests/driver.o
	cc $^ -o $@

tests/pages.gen.s:
	ocaml str.cma tests/makepages.ml $(PAGES) >$@

tests/WebServer.exe: tests/WebServer.gen.o tests/pages.gen.o tests/sys.o tests/driver.o
	cc $^ -o $@

master: tests/sys.c tests/driver32.s tests/RosMaster32.gen.s
	mkdir -p /tmp/master
	-rm /tmp/master/*
	cp tests/sys.c /tmp/master
	cp tests/driver32.s /tmp/master/driver.s
	cp tests/RosMaster32.gen.s /tmp/master/RosMaster.s
	cp Makefile.ros /tmp/master/Makefile
	cd /tmp ; tar zcf master.tgz master

LIB := tests
CITO_EXAMPLES_DIR := cito/examples

$(CITO_EXAMPLES_DIR)/%.gen.ml: $(CITO_EXAMPLES_DIR)/%AMD64.v $(CITO_EXAMPLES_DIR)/%Driver.vo $(LIB)/ignoreFail.ml $(LIB)/printCode.ml Makefile
	cat $(LIB)/ignoreFail.ml >$@
	$(COQC) $< 2>/dev/null \
		| sed '/let coq_Unnamed_thm_/,/module/{/module/!d}' \
		| sed 's/   allWords_def/   fun _ -> []/' \
		| sed 's/   N.to_nat$$/   fun _ -> O/' \
		| sed 's/let rec nuke/type set = unit\n\nlet rec nuke/' \
		>>$@
	cat $(LIB)/printCode.ml >>$@

$(CITO_EXAMPLES_DIR)/%.gen.s: $(CITO_EXAMPLES_DIR)/%.gen.ml
	echo "	.data" >$@
	echo "	.global bedrock_heap" >>$@
	echo "bedrock_heap:" >>$@
	echo "	.fill 4*(1024+50),1,0" >>$@
	echo >>$@
	echo "	.text" >>$@
	echo "	.global main_main" >>$@
	echo >>$@
	ocaml -w -x $< >>$@

$(CITO_EXAMPLES_DIR)/%.exe: %.gen.o $(LIB)/sys.o $(LIB)/driver.o
	cc $^ -o $@
