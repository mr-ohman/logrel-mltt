## HTML Output ############################################################

htmldir=/tmp/logrel-mltt/html

.PHONY : html loc agda-loc agda-woc

html :
	agda --html --html-dir=$(htmldir) Everything.agda


## Lines of Code ##########################################################

agdalocfiles=$(shell find . \( \( -name '*.agda' \) ! -name '.*' \) )

# Agda files in this project

loc : agda-loc

agda-loc :
	@wc $(agdalocfiles)

agda-woc :
	@wc -L $(agdalocfiles)

# EOF
