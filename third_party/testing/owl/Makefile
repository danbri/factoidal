
all:
	@echo "do you mean 'make sync' ?"

sync:
	wget -N -r -np --no-host-directories --cut-dirs=1 --directory-prefix=. http://owl.semanticweb.org/exports/
	find . -name 'index*html*' -exec rm '{}' \;
