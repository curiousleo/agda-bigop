AGDA=agda
AFLAGS=-i../Dependencies/agda-stdlib/src -i../src -i. --latex --latex-dir=. --allow-unsolved-metas
SOURCE=Report
LATEX=latexmk -xelatex # -pdf -use-make -e '$$pdflatex=q/xelatex %O %S/'

all:
	$(AGDA) $(AFLAGS) $(SOURCE).lagda
	$(LATEX) $(SOURCE).tex
