abstract.pdf: abstract.tex Context.tex Syntax.tex
	latexmk -pdf -g abstract
%.tex: %.lagda
	agda --latex --latex-dir=. -i . -i ${AGDALIBDIR} $<