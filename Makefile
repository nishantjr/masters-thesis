thesis.pdf: thesis.md thesis.tex
	export TEXINPUTS=.:$(CURDIR)/uiucthesis2014: && \
	pandoc thesis.md -o thesis.pdf -t latex --template=thesis.tex
