CCT=ocamlbuild -cflags -ppx,"../ppx_listlike"

ppx_listlike:main.native
	mv main.native ppx_listlike

all: ppx_listlike tests

main.native:src/main.ml
	ocamlbuild -pkg compiler-libs.common main.native

tests: tests/test.native tests/example.native

tests/test.native: tests/test.ml src/main.ml
	$(CCT)  test.native

tests/example.native: tests/example.ml src/main.ml
	$(CCT)  example.native
clean:
	ocamlbuild -clean
