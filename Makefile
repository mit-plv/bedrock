MODULE:=Bedrock

.PHONY: default examples platform cito facade src clean native ltac version dist time install install-platform install-cito install-facade install-facade-all install-src install-examples

default: examples

# BEWARE: This will probably take a long time (and may require up to 11GB of memory)!
examples: src
	$(MAKE) -C examples

platform cito facade: src
	$(MAKE) -C platform $@

src:
	$(MAKE) -C src/reification
	$(MAKE) -C src

clean:
	$(MAKE) -C src/reification clean
	$(MAKE) -C src clean
	$(MAKE) -C examples clean
	$(MAKE) -C platform clean

native:
	$(MAKE) -C src native

ltac:
	$(MAKE) -C src ltac

version:
	$(MAKE) -C src version

dist:
	hg archive -t tgz /tmp/bedrock.tgz

install-src:
	$(MAKE) -C src/reification install
	$(MAKE) -C src install

install-platform:
	$(MAKE) -C platform install-platform

install-facade:
	$(MAKE) -C platform install-facade

install-facade-all:
	$(MAKE) -C platform install-facade-all

install-cito:
	$(MAKE) -C platform install-cito

install-examples:
	$(MAKE) -C examples install

install: install-src install-platform install-facade install-cito install-facade-all install-examples

.dir-locals.el: tools/dir-locals.el Makefile
	@ sed s,PWD,$(shell pwd -P),g tools/dir-locals.el | sed s,MOD,$(MODULE),g > .dir-locals.el

time:
	@ rm -rf timing
	@ ./tools/timer.py timing/ src/*.v examples/*.v src/*/*.v
	@ cp Makefile timing/Makefile
	@ cp -r src/Makefile src/Makefile.coq src/reification/ timing/src
	@ cp examples/Makefile examples/Makefile.coq timing/examples
	@ (cd timing; $(MAKE) all)
