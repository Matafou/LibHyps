
lib:
	make -C LibHyps

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

