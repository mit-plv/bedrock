.PHONY: all clean

BEDROCK = -R ../src Bedrock
ARGS = $(BEDROCK) -I ../examples

all: tutorial.pdf Tutorial.html

tutorial.pdf: tutorial.tex Tutorial.v.tex Makefile
	pdflatex tutorial

Tutorial.v.tex: Tutorial.vo Makefile
	coqdoc -s --body-only --latex $(BEDROCK) Tutorial.v -o Tutorial.v.tex

Tutorial.html: Tutorial.vo Makefile
	coqdoc -s --html $(BEDROCK) Tutorial.v

Tutorial.vo: Tutorial.v Makefile
	coqc $(ARGS) Tutorial
