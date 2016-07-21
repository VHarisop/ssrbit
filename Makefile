.PHONY=all clean tests

OCB=ocamlbuild -use-ocamlfind

all: build extraction tests

build: Makefile.coq
	$(MAKE) -f Makefile.coq

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq

extraction: extraction/STAMP

# XXX: This will force the recompilation of refinement/bits.vo
# as it depends on extraction/axioms.vo
extraction/STAMP: build extraction/axioms.v
	rm -f test_*.ml test_*.mli extraction/axioms.vo
	$(MAKE) -f Makefile.coq extraction/axioms.vo
	mv test_*.ml* extraction/
	touch extraction/STAMP

TEST_FILES=$(addprefix extraction/test_int,8 16 32)
TEST_BYTE:=$(TEST_FILES:=.byte)
TEST_NATIVE:=$(TEST_FILES:=.native)

test:
	mkdir -p test

tests: test extraction $(addsuffix .ml, $(TEST_FILES))
	$(OCB) -package unix $(TEST_NATIVE)

clean: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	$(OCB) -clean
	rm -rf Makefile.coq extraction/test_* extraction/STAMP
