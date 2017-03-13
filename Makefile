abstract.pdf: abstract.tex Context.tex Syntax.tex type.bib
	latexmk -pdf -g abstract
%.tex: %.lagda
	agda --latex --latex-dir=. -i . -i ${AGDALIBDIR} $<