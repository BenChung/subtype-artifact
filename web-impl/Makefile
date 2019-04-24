default:
	ocamlbuild -use-menhir -use-ocamlfind -plugin-tag "package(js_of_ocaml.ocamlbuild)" -package js_of_ocaml-ppx -pkg js_of_ocaml subtype.js
	cp _build/subtype.js ./js/

deps: 
	opam install ocamlbuild menhir js_of_ocaml js_of_ocaml-compiler js_of_ocaml-lwt js_of_ocaml-ppx js_of_ocaml-ocamlbuild
