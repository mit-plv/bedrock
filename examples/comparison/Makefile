compare: gen.exe
	./gen.exe $(DATA) $(CMD)
	$(MAKE) c.exe ocaml.exe ocaml_nice.exe
	time ./c.exe >/dev/null
	time ./ocaml.exe >/dev/null
	time ./ocaml_nice.exe >/dev/null

verify: gen.exe
	./gen.exe $(DATA) $(CMD)
	$(MAKE) c.exe ocaml.exe ocaml_nice.exe
	./c.exe >/tmp/c.txt
	./ocaml.exe >/tmp/ocaml.txt
	./ocaml_nice.exe >/tmp/ocaml_nice.txt
	diff /tmp/c.txt /tmp/ocaml.txt
	diff /tmp/c.txt /tmp/ocaml_nice.txt

.PHONY: compare verify

gen.exe: gen.ml
	ocamlopt gen.ml -o gen.exe

c.exe: server.o data.o driver.o
	gcc server.o data.o driver.o -o c.exe

ocaml.exe: ocaml_server.ml ocaml_data.ml ocaml_driver.ml
	ocamlopt ocaml_server.ml ocaml_data.ml ocaml_driver.ml -o ocaml.exe

ocaml_nice.exe: ocaml_nice_server.ml ocaml_data.ml ocaml_nice_driver.ml
	ocamlopt ocaml_nice_server.ml ocaml_data.ml ocaml_nice_driver.ml -o ocaml_nice.exe

Server.vo: Server.v ../AutoSep.vo ../SinglyLinkedList.vo ../Malloc.vo
	coqc -q -I .. -R ../../src Bedrock Server
