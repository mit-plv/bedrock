ROOT    := ..
MODULES := Conditional AutoSepExt PreAutoSep \
           Util \
           AutoSep Misc \
           Malloc \
           Bags Sets Queue ThreadQueue ThreadQueues Scheduler Thread \
           Bootstrap SinglyLinkedList \
           tests/Thread0 \
           tests/LinkTest tests/BabyThread tests/Yield tests/Spawn tests/ListBuilder tests/SharedList \
           tests/BabyThreadDriver tests/ListBuilderDriver tests/SharedListDriver

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

tests/listbuilder.s: tests/ListBuilderAMD64.v
	echo ".global bedrock_heap" >$@
	echo ".comm bedrock_heap,4*(1024+50+1)" >>$@
	echo ".global main_main" >>$@
	echo >>$@
	$(COQC) $< \
		| sed 's/^.*:: nil//' \
		| sed 's/^.*:: *//' \
		| sed 's/^.*: list string//' \
		| sed 's/^.*= "//' \
		| sed 's/^.*"//' \
		>>$@

tests/listbuilder.exe: tests/listbuilder.o tests/driver.o
	gcc tests/listbuilder.o tests/driver.o -o $@

tests/sharedlist.s: tests/SharedListAMD64.v
	echo ".global bedrock_heap" >$@
	echo ".comm bedrock_heap,4*(1024+50+2)" >>$@
	echo ".global main_main" >>$@
	echo >>$@
	$(COQC) $< \
		| sed 's/^.*:: nil//' \
		| sed 's/^.*:: *//' \
		| sed 's/^.*: list string//' \
		| sed 's/^.*= "//' \
		| sed 's/^.*"//' \
		>>$@

tests/sharedlist.exe: tests/sharedlist.o tests/driver.o
	gcc tests/sharedlist.o tests/driver.o -o $@
