FILE1="term1"
FILE2="term2"

all:
	@echo targets are term1, term2, term1_dot, term2_dot

term1:
	runpcal -termination $(FILE1)
	runtla -dump dot,colorize,actionlabels $(FILE1).dot $(FILE1)

term1_dot: all
	dot $(FILE1).dot -o$(FILE1).pdf -Tpdf
	open -a /System/Applications/Preview.app $(FILE1).pdf

term2:
	runpcal -termination $(FILE2)
	runtla -dump dot,colorize,actionlabels $(FILE2).dot $(FILE2)

term2_dot: all
	dot $(FILE2).dot -o$(FILE2).pdf -Tpdf
	open -a /System/Applications/Preview.app $(FILE2).pdf

clean:
	rm -rf ./states $(FILE1).old ./*.dot $(FILE1).pdf
