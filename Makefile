MODULE:=Bedrock

.PHONY: all clean dist native ltac version

all:
	# BEWARE: This will probably take a long time (and may require up to 4GB of memory)!
	$(MAKE) -C src/reification
	$(MAKE) -C src
	$(MAKE) -C examples

cito:
	# BEWARE: This will probably take a long time (and may require up to 4GB of memory)!
	$(MAKE) -C src/reification
	$(MAKE) -C src
	$(MAKE) -C platform -f Makefile.cito

clean:
	$(MAKE) -C src/reification clean
	$(MAKE) -C src clean
	$(MAKE) -C examples clean
	$(MAKE) -C platform clean
	$(MAKE) -C platform clean -f Makefile.cito

native:
	$(MAKE) -C src native

ltac:
	$(MAKE) -C src ltac

version:
	$(MAKE) -C src version

dist:
	hg archive -t tgz /tmp/bedrock.tgz

.dir-locals.el: tools/dir-locals.el Makefile
	@ sed s,PWD,$(shell pwd -P),g tools/dir-locals.el | sed s,MOD,$(MODULE),g > .dir-locals.el

time:
	@ rm -rf timing
	@ ./tools/timer.py timing/ src/*.v examples/*.v src/*/*.v
	@ cp Makefile timing/Makefile
	@ cp -r src/Makefile src/Makefile.coq src/reification/ timing/src 
	@ cp examples/Makefile examples/Makefile.coq timing/examples
	@ (cd timing; $(MAKE) all)
