FILE="deadlock"

deadlock1:
	runpcal $(FILE)
	runtla -dump dot,colorize,actionlabels $(FILE).dot $(FILE)
	dot $(FILE).dot -o$(FILE).pdf -Tpdf

clean:
	rm -rf ./states ./*.old ./*.dot ./*.pdf
