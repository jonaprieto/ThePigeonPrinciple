
all:
	@agda --latex --allow-unsolved-metas PigeonPrincipleInUTT.lagda &&\
	 latexmk -pdf -xelatex latex/PigeonPrincipleInUTT.tex

clean:
	- @latexmk -c latex/PigeonPrincipleInUTT.tex
	- @latexmk -c PigeonPrincipleInUTT.lagda
	- @rm -f *.nav
	- @rm -f *.out
	- @rm -f *.blg
	- @rm -f *.bbl
	- @rm -f *.fdb_latexmk
	- @rm -f *.fls
	- @rm -f *.lagda~
	- @rm -f *.ptb
	- @rm -f *.log
	- @rm -f *.bcf
	- @rm -f *.aux
	- @rm -f *.xdv
	- @rm -f *.dvi
	- @rm -f *.run.xml
	- @rm -f *.snm
	- @rm -f *.toc
	- @rm -f *.agdai
	- @rm -f *.synctex.gz
