

all: lib tests

lib:
	make -C LibHyps

tests-lib:
	make -C tests

tests: lib
	make -C tests

clean:
	make -C LibHyps clean
	make -C tests clean

install:
	make -C LibHyps install

