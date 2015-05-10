ppx_listlike:main.native
	mv main.native ppx_listlike

all: ppx_listlike tests/test.native

main.native:src/main.ml
	ocamlbuild -pkg compiler-libs.common main.native

tests/test.native: tests/test.ml src/main.ml
	ocamlbuild -cflags -ppx,"../ppx_listlike"  test.native

clean:
	ocamlbuild -clean
