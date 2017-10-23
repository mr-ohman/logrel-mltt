## HTML Output ############################################################

htmldir=$(HOME)/popl17/html
# htmldir=/tmp/logrel-mltt/html

# Agda-2.5.3 needed to generate the links we use in the paper
agda=agda-2.5.3

.PHONY : clean pack check agda-check html loc agda-loc agda-woc

html :
	$(agda) --html --html-dir=$(htmldir) Everything.agda


## Type Check Code ########################################################

check : agda-check

# Type check the code

agda-check:
	$(agda) Everything.agda

pack: clean
	mkdir code
	cp -r Definition Tools Everything.agda README.agda Makefile code/
	$(agda) --html Everything.agda
	zip -r formalization code html

clean:
	find . -name "*.agdai" -type f -delete
	rm -rf code html formalization.zip

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
