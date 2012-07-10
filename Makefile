.PHONY: all clean dist native ltac version

all:
	# BEWARE: This will probably take a long time (and may require up to 4GB of memory)!
	$(MAKE) -C src/reification
	$(MAKE) -C src
	$(MAKE) -C examples

clean:
	$(MAKE) -C src/reification clean
	$(MAKE) -C src clean
	$(MAKE) -C examples clean

native:
	$(MAKE) -C src native

ltac:
	$(MAKE) -C src ltac

version:
	$(MAKE) -C src version

dist:
	hg archive -t tgz /tmp/bedrock.tgz

time:
	@ rm -rf timing
	@ ./tools/timer.py timing/ src/*.v examples/*.v src/*/*.v
	@ cp Makefile timing/Makefile
	@ cp src/Makefile src/Makefile.coq timing/src
	@ cp examples/Makefile examples/Makefile.coq timing/examples
	@ (cd timing; $(MAKE) all)