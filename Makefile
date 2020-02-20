
all:
	@agda --latex --allow-unsolved-metas The-pigeonhole-principle-HoTT.lagda &&\
	 latexmk -pdf -xelatex latex/The-pigeonhole-principle-HoTT.tex

clean:
	- @latexmk -c latex/The-pigeonhole-principle-HoTT.tex
	- @latexmk -c The-pigeonhole-principle-HoTT.lagda
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
