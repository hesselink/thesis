SRC = thesis.tex introduction.tex benchmark.tex typeparameters.tex functorrep.tex oneparam.tex multiparam.tex multirec.tex multirecabstract.tex multirecparams.tex composition.tex limitations.tex conclusion.tex thesis.bib

.PHONY : clean

thesis.pdf : $(SRC)
	latexmk -pdf -g $<

%.tex : %.lagda
	lhs2TeX --agda -o $@ $<

%.tex : %.lhs thesis.fmt
	lhs2TeX -o $@ $<

preview :
	latexmk -pdf -pvc thesis

clean :
	latexmk -C
	for file in $(SRC:%.tex=%.lhs); do if [ -e $$file ]; then rm -f $${file%lhs}tex; fi; done
	rm -f thesis.ptb
