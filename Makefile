pdf: main.pdf
.PHONY: pdf

main.pdf: 
	latexmk -pdf main.tex
.PHONY: main.pdf

main.ps: main.pdf
	acroread -toPostScript $<

clean:
	latexmk -C main.tex
	rm *.bbl
.PHONY: clean

view: main.pdf
	open main.pdf
.PHONY: view

safe: main.pdf
	mkdir -p archive
	cp $^ archive/`date "+%y.%m.%d-%H.%M.%S"`-`openssl md5 < $^`.pdf

