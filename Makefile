.PHONY: all clean dist

all:
	# BEWARE: This will probably take a long time!
	$(MAKE) -C src
	$(MAKE) -C examples

clean:
	$(MAKE) -C src clean
	$(MAKE) -C examples clean

dist:
	hg archive -t tgz /tmp/bedrock.tgz

time:
	@ rm -rf timing
	@ ./tools/timer.py timing/ src/*.v examples/*.v src/*/*.v
	@ cp Makefile timing/Makefile
	@ cp src/Makefile src/Makefile.coq timing/src
	@ cp examples/Makefile examples/Makefile.coq timing/examples
	@ (cd timing; $(MAKE) all)