FILE="hash"

all:
	runpcal $(FILE)
	runtla  -dump actionlabels -dump colorize -dump dot $(FILE).dot $(FILE)

dot: all
	dot $(FILE).dot -o$(FILE).pdf -Tpdf
	open -a /System/Applications/Preview.app $(FILE).pdf

pv:
	open -a /System/Applications/Preview.app $(FILE).pdf

clean:
	rm -rf ./states $(FILE).old $(FILE).dot
