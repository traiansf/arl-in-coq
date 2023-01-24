objects := $(patsubst %.md,%.pdf,$(wildcard *.md)) $(patsubst %.md,%.html,$(wildcard *.md))

all: index.html

%.pdf: %.md k.bib Makefile
	pandoc $< -o $@ -s -t beamer --citeproc

index.html: README.md k.bib Makefile
	pandoc $< -o $@ -s -t slidy --toc --toc-depth 2 --citeproc

%.ipynb: %.md
	pandoc $< -o $@

clean:
	-rm $(objects)

.PHONY: all clean
