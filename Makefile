## HTML Output ############################################################

htmldir=/tmp/logrel-mltt/html

.PHONY : html

html :
	agda --html --html-dir=$(htmldir) Everything.agda


## Lines of Code ##########################################################

agdalocfiles=$(shell find . \( \( -name '*.agda' \) ! -name '.*' \) )

# Agda files in this project

agda-loc :
	@wc $(agdalocfiles)

agda-woc :
	@wc -L $(agdalocfiles)

# EOF
