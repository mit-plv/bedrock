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
           tests/Ros tests/MiniMasterDriver tests/RosMasterDriver \
           tests/RtosDriver \
           tests/Increment

VNAME := -name \*.v ! -name \*.\#\*

CITO := $(shell find cito $(VNAME))

FACADE_ALLV := $(shell find facade $(VNAME))

FACADE := \
	facade/Facade \
	facade/DFacade \
	facade/CompileUnit \

FACADE_ALL := \
	facade/examples/FiatADTs \
	facade/examples/FiatRepInv \
	facade/examples/FiatImpl \
	facade/DFacadeToBedrock \

.PHONY: default platform cito facade facade_all facade_allv build clean master install install-platform install-cito install-facade install-facade-all rtos32 rtos64
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

facade_allv: T=$(FACADE_ALLV)
facade_allv: build

COQARGS := -R $(ROOT)/src Bedrock -I . -I tests -R cito Cito -R facade Facade

COQC    := $(COQBIN)coqc $(COQARGS)

# N.B. (Jason Gross): This Makefile does not consistently support
# building cito and facade simultaneously with multiple threads; the
# Makefile.coqs will overwrite each other
build:
	$(COQBIN)coq_makefile $(COQARGS) $(addsuffix .v,$(basename $(T))) -o Makefile.coq
	@echo '-include $(addsuffix .d,$(shell find . -name \*.v ! -name \*.#\*))' >> Makefile.coq
	$(MAKE) -f Makefile.coq

# we want to install everything, so we need to remake the makefile
install:
	$(COQBIN)coq_makefile $(COQARGS) $(addsuffix .v,$(basename $(FACADE_ALLV) $(CITO) $(MODULES))) -o Makefile.coq
	$(MAKE) -f Makefile.coq install

install-facade:
	$(COQBIN)coq_makefile $(COQARGS) $(addsuffix .v,$(basename $(FACADE))) -o Makefile.coq
	$(MAKE) -f Makefile.coq install

install-facade-all:
	$(COQBIN)coq_makefile $(COQARGS) $(addsuffix .v,$(basename $(FACADE_ALL))) -o Makefile.coq
	$(MAKE) -f Makefile.coq install

install-facade-allv:
	$(COQBIN)coq_makefile $(COQARGS) $(addsuffix .v,$(basename $(FACADE_ALLV))) -o Makefile.coq
	$(MAKE) -f Makefile.coq install

install-cito:
	$(COQBIN)coq_makefile $(COQARGS) $(addsuffix .v,$(basename $(CITO))) -o Makefile.coq
	$(MAKE) -f Makefile.coq install

install-platform:
	$(COQBIN)coq_makefile $(COQARGS) $(addsuffix .v,$(basename $(MODULES))) -o Makefile.coq
	$(MAKE) -f Makefile.coq install

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

tests/Rtos.exe: tests/Rtos.gen.o tests/sys.o tests/driver.o tests/rtos.o tests/rtos_app.o
	cc $^ -o $@

tests/Rtos.gen.s: tests/Rtos.gen.ml tests/Rtos.txt
	echo "	.data" >$@
	echo "	.global bedrock_heap" >>$@
	echo "bedrock_heap:" >>$@
	echo "	.fill 4*(1024*1024*200+50+`cat tests/Rtos.txt`),1,0" >>$@
	echo >>$@
	echo "	.text" >>$@
	echo "	.global main_main,scheduler_init,scheduler_spawn,scheduler_exit,scheduler_yield,scheduler_listen,scheduler_close,scheduler_read,scheduler_write,scheduler_accept,scheduler_connect,scheduler_connected" >>$@
	echo >>$@
	ocaml -w -x $< >>$@

tests/Rtos32.gen.s: tests/Rtos32.gen.ml tests/Rtos.txt
	echo "	.data" >$@
	echo "	.global bedrock_heap" >>$@
	echo "bedrock_heap:" >>$@
	echo "	.fill 4*(1024*1024*200+50+`cat tests/Rtos.txt`),1,0" >>$@
	echo >>$@
	echo "	.text" >>$@
	echo "	.global main_main,scheduler_init,scheduler_spawn,scheduler_exit,scheduler_yield,scheduler_listen,scheduler_close,scheduler_read,scheduler_write,scheduler_accept,scheduler_connect,scheduler_connected" >>$@
	echo >>$@
	ocaml -w -x $< >>$@

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

rtos64: tests/sys.c tests/driver.s tests/Rtos.gen.s tests/rtos.s tests/bedrock.h tests/rtos_app.c
	mkdir -p /tmp/brtos64
	-rm /tmp/brtos64/*
	cp README.rtos /tmp/brtos64/README
	cp tests/sys.c /tmp/brtos64/
	cp tests/driver.s /tmp/brtos64/
	cp tests/Rtos.gen.s /tmp/brtos64/bedrock.s
	cp Makefile.rtos64 /tmp/brtos64/Makefile
	cp tests/bedrock.h /tmp/brtos64/
	cp tests/rtos_app.c /tmp/brtos64/
	cp tests/rtos.s /tmp/brtos64/
	cd /tmp ; tar zcf brtos64.tgz brtos64

rtos32: tests/sys.c tests/driver32.s tests/Rtos32.gen.s tests/rtos32.s tests/bedrock.h tests/rtos_app.c
	mkdir -p /tmp/brtos32
	-rm /tmp/brtos32/*
	cp README.rtos /tmp/brtos32/README
	cp tests/sys.c /tmp/brtos32/
	cp tests/driver32.s /tmp/brtos32/driver.s
	cp tests/Rtos32.gen.s /tmp/brtos32/bedrock.s
	cp Makefile.rtos32 /tmp/brtos32/Makefile
	cp tests/bedrock.h /tmp/brtos32/
	cp tests/rtos_app.c /tmp/brtos32/
	cp tests/rtos32.s /tmp/brtos32/rtos.s
	cd /tmp ; tar zcf brtos32.tgz brtos32
