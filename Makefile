SRC = thesis.tex introduction.tex benchmark.tex typeparameters.tex functorrep.tex oneparam.tex multiparam.tex multirec.tex applications.tex

.PHONY : clean

thesis.pdf : $(SRC)
	latexmk -pdf -g $<

%.tex : %.lagda
	lhs2TeX --agda -o $@ $<

%.tex : %.lhs
	lhs2TeX -o $@ $<

preview :
	latexmk -pdf -pvc thesis

clean :
	latexmk -C
	for file in $(SRC:%.tex=%.lhs); do if [ -e $$file ]; then rm -f $${file%lhs}tex; fi; done
	rm -f thesis.ptb
