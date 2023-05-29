DOC = main
PDFLATEX = pdflatex --shell-escape
BIBTEX = bibtex

all: $(DOC).pdf

$(DOC).pdf: $(DOC).tex $(DOC).aux $(DOC).bbl
	$(PDFLATEX) $(DOC)

$(DOC).aux: $(DOC).tex
	$(PDFLATEX) $(DOC)

$(DOC).bbl: $(DOC).aux $(DOC).bib
	$(BIBTEX) $(DOC)

clean:
	rm -f *.aux *.log *.out *.toc *.bbl *.blg *.lof *.lot *.synctex.gz *.fdb_latexmk *.fls

.PHONY: all clean
