## HTML Output ############################################################

htmldir=/tmp/logrel-mltt/html

.PHONY : html loc agda-loc agda-woc

html :
	agda --html --html-dir=$(htmldir) Everything.agda


## Lines of Code ##########################################################

agdalocfiles=$(shell find . \( \( -name '*.agda' \) ! -name '.*' \) )

# Agda files in this project

loc : agda-loc
nc  : agda-loc-nc

# Sum all agda files

agda-loc :
	@wc $(agdalocfiles)

# Delete comments (sed) and empty lines (grep .) first

agda-loc-nc :
	@sed -e '/--.*/d' $(agdalocfiles) | grep . | wc

# Find the widest column:

agda-woc :
	@wc -L $(agdalocfiles)

# EOF
