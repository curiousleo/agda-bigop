AGDA=agda
AFLAGS=-i../Dependencies/agda-stdlib/src -i../src -i. --latex --latex-dir=.
SOURCE=Report
POSTPROCESS=postprocess-latex.pl
LATEX=latexmk -xelatex # -pdf -use-make -e '$$pdflatex=q/xelatex %O %S/'

all:
	$(AGDA) $(AFLAGS) $(SOURCE).lagda
#	cd latex/ && \
#	perl ../$(POSTPROCESS) $(SOURCE).tex > $(SOURCE).processed && \
#	mv $(SOURCE).processed $(SOURCE).tex && \
#	$(LATEX) $(SOURCE).tex && \
#	mv $(SOURCE).pdf ..
	$(LATEX) $(SOURCE).tex
