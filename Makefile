SRC = thesis.tex introduction.tex benchmark.tex typeparameters.tex applications.tex

.PHONY : clean

thesis.pdf : $(SRC)
	latexmk -pdf -g $<

%.tex : %.lhs
	lhs2TeX -o $@ $<

clean :
	latexmk -CA
	for file in $(SRC:%.tex=%.lhs); do if [ -e $$file ]; then rm -f $${file/%lhs/tex}; fi; done
