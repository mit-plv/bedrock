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
