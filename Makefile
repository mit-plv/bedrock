.PHONY: all clean dist

all:
	# BEWARE: This will probably take a long time!
	$(MAKE) -C src

clean:
	$(MAKE) -C src clean

dist:
	hg archive -t tgz /tmp/bedrock.tgz
