FILE1="term"

term1:
	runpcal $(FILE1)
	runtla -dump dot,colorize,actionlabels $(FILE1).dot $(FILE1)

term2:
	runpcal -termination $(FILE1)
	runtla -dump dot,colorize $(FILE1).dot $(FILE1)

clean:
	rm -rf ./states $(FILE1).old ./*.dot $(FILE1).pdf
