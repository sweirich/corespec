# Simple makefile to render the spec as pdf
all: spec

spec:
	ott -i ett.ott -o ett.tex
	sed -i '6i \\\input{pkgs.tex}' ett.tex
	pdflatex ett.tex -interaction batchmode > pdflatex.log
	rm ett.tex

clean:
	rm ett.pdf pdflatex.log