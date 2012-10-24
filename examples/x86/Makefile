all: factorial.exe

.PHONY: all

COQC = coqc -R ../../src Bedrock -I ..

factorial.s: FactorialX86.v
	echo ".global bedrock_heap" >$@
	echo ".comm bedrock_heap,4096,32" >>$@
	echo ".global fact_fact" >>$@
	echo >>$@
	$(COQC) $< \
		| sed 's/^.*= "//' \
		| sed 's/^"//' \
		| sed 's/^.*: string//' \
		>>$@

factorial.exe: factorial.o factorial_driver.o
	gcc factorial.o factorial_driver.o -o $@
