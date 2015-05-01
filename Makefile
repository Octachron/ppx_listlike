ppx_listlike:main.native
	mv main.native ppx_listlike

all: ppx_listlike tests/test.native

main.native:main.ml
	ocamlbuild -pkg compiler-libs.common main.native

tests/test.native:
	ocamlbuild -cflags -ppx,"../ppx_listlike"  tests/test.native
