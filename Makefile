
ipeImages    := $(wildcard ./../docs/ipe-images/*.ipe)
ipeImagesPNG := $(subst ./../docs/ipe-images/,./../docs/ipe-images/,$(subst .ipe,.png,$(ipeImages)))

all: $(ipeImagesPNG)
	@agda --latex --allow-unsolved-metas GTheory.lagda &&\
	 latexmk -pdf -xelatex latex/GTheory.tex

palomar :
	@agda --latex --allow-unsolved-metas PigeonPrincipleInUTT.lagda &&\
	 latexmk -pdf -xelatex latex/PigeonPrincipleInUTT.tex


../docs/ipe-images/%.png: ../docs/ipe-images/%.ipe
	iperender -png -resolution 400 $< $@

clean:
	- @latexmk -c latex/GTheory.tex
	- @latexmk -c GTheory.lagda
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
