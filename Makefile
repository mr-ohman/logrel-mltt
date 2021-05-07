## HTML Output ############################################################

htmldir=html
# htmldir=$(HOME)/popl17/html
# htmldir=/tmp/logrel-mltt/html

# Agda-2.5.3 needed to generate the links we use in the paper
# Agda-2.5.4 ok from 2018-02-19
# try latest Agda
agda=time agda +RTS -s -RTS -v profile:7
main=Logrel-MLTT.agda

.PHONY : clean pack check agda-check html loc agda-loc agda-woc

html :
	$(agda) --html --html-dir=$(htmldir) $(main)


## Type Check Code ########################################################

check : agda-check

# Type check the code

agda-check:
	$(agda) $(main)

pack: clean
	mkdir code
	cp -r Definition Tools $(main) README.agda Makefile code/
	$(agda) --html $(main)
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
