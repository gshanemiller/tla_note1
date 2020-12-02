FILE="hash"

all:
	runpcal $(FILE)
	runtla -dump dot,colorize,actionlabels $(FILE).dot -coverage 1 $(FILE)

dot: all
	dot $(FILE).dot -o$(FILE).pdf -Tpdf
	open -a /System/Applications/Preview.app $(FILE).pdf

pv:
	open -a /System/Applications/Preview.app $(FILE).pdf

clean:
	rm -rf ./states $(FILE).old ./*.dot $(FILE).pdf
