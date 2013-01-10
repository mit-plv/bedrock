ROOT    := ..
MODULES := AutoSepExt PreAutoSep \
           Util \
           AutoSep RecPred \
           Malloc \
           Bags Queue ThreadQueue Thread \
           Bootstrap SinglyLinkedList \
           tests/Thread0 \
           tests/LinkTest tests/BabyThread tests/Yield tests/Spawn tests/ListBuilder tests/SharedList \
           tests/BabyThreadDriver tests/ListBuilderDriver

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
	echo ".comm bedrock_heap,4096,32" >>$@
	echo ".global main_main" >>$@
	echo >>$@
	$(COQC) $< \
		| sed 's/^.*= "//' \
		| sed 's/^"//' \
		| sed 's/^.*: string//' \
		>>$@

tests/listbuilder.exe: tests/listbuilder.o tests/driver.o
	gcc tests/listbuilder.o tests/driver.o -o $@
