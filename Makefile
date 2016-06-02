
## Lines of Code ##########################################################

agdalocfiles=$(shell find . \( \( -name '*.agda' \) ! -name '.*' \) )

# Agda files in this project

agda-loc :
	@wc $(agdalocfiles)
