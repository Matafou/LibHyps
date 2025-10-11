
.PHONY: tests LibHyps

lib: sanity
	make -C LibHyps

# Use this instead of make lib when the debug code is present
make debug:
	make -C LibHyps
	make -C tests

tests: lib
	make -C tests

all: lib tests

tests-nolib:
	make -C tests

clean:
	make -C LibHyps clean
	make -C tests clean

# Don't install test files
install: lib
	make -C LibHyps install

sanity:
	@./testDebug.sh
