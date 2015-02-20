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

CITO := $(shell find Cito $(VNAME))

FACADE_ALLV := $(shell find Facade $(VNAME))

FACADE := \
	Facade/Facade \
	Facade/DFacade \
	Facade/CompileUnit \

FACADE_ALL := \
	Facade/examples/FiatADTs \
	Facade/examples/FiatRepInv \
	Facade/examples/FiatImpl \
	Facade/DFacadeToBedrock \

MODULES_V := $(addsuffix .v,$(MODULES))
CITO_V := $(CITO)
#FACADE_ALLV := $(FACADE_ALLV)
FACADE_V := $(addsuffix .v,$(FACADE))
FACADE_ALL_V := $(addsuffix .v,$(FACADE_ALL))

ALL_V := $(sort $(MODULES_V) $(CITO_V) $(FACADE_ALLV) $(FACADE_V) $(FACADE_ALL_V))

MODULES_VO := $(addsuffix .vo,$(MODULES))
CITO_VO := $(patsubst %.v,%.vo,$(CITO))
FACADE_ALLVO := $(patsubst %.v,%.vo,$(FACADE_ALLV))
FACADE_VO := $(addsuffix .vo,$(FACADE))
FACADE_ALL_VO := $(addsuffix .vo,$(FACADE_ALL))

MODULES_VIO := $(addsuffix .vio,$(MODULES))
CITO_VIO := $(patsubst %.v,%.vio,$(CITO))
FACADE_ALLVIO := $(patsubst %.v,%.vio,$(FACADE_ALLV))
FACADE_VIO := $(addsuffix .vio,$(FACADE))
FACADE_ALL_VIO := $(addsuffix .vio,$(FACADE_ALL))


.PHONY: default platform cito facade facade_all facade_allv \
	quick platform-quick cito-quick facade-quick facade_all-quick facade_allv-quick \
	vio2vo platform-vio2vo cito-vio2vo facade-vio2vo facade_all-vio2vo facade_allv-vio2vo \
	selective-install selective-vio2vo \
	build clean master install install-platform install-cito install-facade install-facade-all rtos32 rtos64
.PRECIOUS: tests/%.gen.ml tests/%.gen.s

default: platform

COQARGS := -R $(ROOT)/src Bedrock -R . Bedrock.Platform

# we make Makefile.coq depend on all .v files, as a hack for getting it to depend on the *list* of .v files
Makefile.coq: Makefile $(ALL_V)
	$(COQBIN)coq_makefile $(COQARGS) $(ALL_V) > Makefile.coq

-include Makefile.coq

platform: $(MODULES_VO)
platform-quick: $(MODULES_VIO)
platform-vio2vo: T=$(MODULES)
platform-vio2vo: selective-vio2vo
install-platform: T=$(MODULES)
install-platform: selective-install

cito: $(CITO_VO)
cito-quick: $(CITO_VIO)
cito-vio2vo: T=$(CITO)
cito-vio2vo: selective-vio2vo
install-cito: T=$(CITO)
install-cito: selective-install

facade: $(FACADE_VO)
facade-quick: $(FACADE_VIO)
facade-vio2vo: T=$(FACADE)
facade-vio2vo: selective-vio2vo
install-facade: T=$(FACADE)
install-facade: selective-install

facade_all: $(FACADE_ALL_VO)
facade_all-quick: $(FACADE_ALL_VIO)
facade_all-vio2vo: T=$(FACADE_ALL)
facade_all-vio2vo: selective-vio2vo
install-facade_all: T=$(FACADE_ALL)
install-facade_all: selective-install

facade_allv: $(FACADE_ALLVO)
facade_allv-quick: $(FACADE_ALLVIO)
facade_allv-vio2vo: T=$(FACADE_ALLV)
facade_allv-vio2vo: selective-vio2vo
install-facade_allv: T=$(FACADE_ALLV)
install-facade_allv: selective-install

selective-vio2vo:
	$(COQC) $(COQDEBUG) $(COQFLAGS) -schedule-vio2vo $(J) $(addsuffix .vio,$(basename $(T)))

selective-install:
	cd "." && for i in $(addsuffix .vo,$(basename $(T))) $(addsuffix .v,$(basename $(T))) $(addsuffix .glob,$(basename $(T))); do \
	 install -d "`dirname "$(DSTROOT)"$(COQLIBINSTALL)/Bedrock/$$i`"; \
	 install -m 0644 $$i "$(DSTROOT)"$(COQLIBINSTALL)/Bedrock/$$i; \
	done


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
CITO_EXAMPLES_DIR := Cito/examples

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
