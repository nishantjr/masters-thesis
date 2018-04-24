thesis-readable.pdf: thesis.md easy-to-read.tex algorithm.tex hfs.tex
	export TEXINPUTS=.:$(CURDIR)/uiucthesis2014: && \
	pandoc $< -o $@ -t latex -f markdown+line_blocks --filter ./include.hs --template=easy-to-read.tex

thesis-formatted.pdf: thesis.md official-format.tex algorithm.tex hfs.tex
	export TEXINPUTS=.:$(CURDIR)/uiucthesis2014: && \
	pandoc $< -o $@ -t latex -f markdown+line_blocks --filter ./include.hs --template=official-format.tex

hfs.tex: maude/contrib/systems.md/hereditarily-finite-set.md extract-class.lua
	pandoc -t latex --lua-filter extract-class.lua -o $@ $< 
algorithm.tex: maude/contrib/tools/meta.md/nelson-oppen-combination.md extract-class.lua
	pandoc -t latex --lua-filter extract-class.lua -o $@ $< 
