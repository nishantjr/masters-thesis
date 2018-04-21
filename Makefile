thesis-readable.pdf: thesis.md easy-to-read.tex
	export TEXINPUTS=.:$(CURDIR)/uiucthesis2014: && \
	pandoc $< -o $@ -t latex -f markdown+line_blocks --filter ./include.hs --template=easy-to-read.tex

thesis-formatted.pdf: thesis.md official-format.tex
	export TEXINPUTS=.:$(CURDIR)/uiucthesis2014: && \
	pandoc $< -o $@ -t latex -f markdown+line_blocks --filter ./include.hs --template=official-format.tex

