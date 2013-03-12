ROOT    := ..
MODULES := Conditional AutoSepExt PreAutoSep \
           Util \
           AutoSep Misc \
           Sys Safety \
           Malloc \
           Bags Sets Queue ThreadQueue ThreadQueues SinglyLinkedList Scheduler Thread \
           Bootstrap Arrays8 MoreArrays \
           tests/Thread0 tests/Io \
           tests/LinkTest tests/Abort tests/PrintInt tests/ArrayTest tests/Echo tests/Echo2 \
           tests/AbortDriver tests/PrintIntDriver tests/ArrayTestDriver tests/EchoDriver tests/Echo2Driver \
           tests/BabyThread tests/Yield tests/Spawn tests/ListBuilder tests/SharedList tests/Echo3 \
           tests/BabyThreadDriver tests/ListBuilderDriver tests/SharedListDriver tests/Echo3Driver

VS      := $(MODULES:%=%.v)

.PHONY: coq clean

coq: Makefile.coq
	$(MAKE) -f Makefile.coq

COQARGS := -R $(ROOT)/src Bedrock -I tests
COQC    := coqc $(COQARGS)

Makefile.coq: Makefile $(VS)
	coq_makefile $(COQARGS) $(VS) -o Makefile.coq

clean:: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq .depend

tests/%.gen.s: tests/%AMD64.v tests/%Driver.vo tests/%.txt
	echo ".global bedrock_heap" >$@
	echo ".comm bedrock_heap,4*(1024+50+`cat tests/$*.txt`)" >>$@
	echo ".global main_main" >>$@
	echo >>$@
	$(COQC) $< \
		| sed 's/^.*:: nil//' \
		| sed 's/^.*:: *//' \
		| sed 's/^.*: list string//' \
		| sed 's/^.*= "//' \
		| sed 's/^.*"//' \
		>>$@

tests/%.exe: tests/%.gen.o tests/sys.o tests/driver.o
	cc $^ -o $@

.PRECIOUS: %.gen.s
