all: configure coq interpreter

configure: coq/configure coq/*.v
	cd coq;	./configure

coq: configure
	make -C coq/

copy_ljs:
	mkdir -p build/
	cp caml/ljs/ljs_lexer.mll caml/ljs/ljs_parser.mly build/

edit_ljs:
	# You might want the following commands if you want to use the latest
	# version of LambdaJS' files. They are not enough to make the files
	# compatible with our implementation, but they help a lot.
	sed -i "s/open Prelude/(* open Prelude *)/" build/ljs_{parser.mly,lexer.mll}
	sed -i "s/Pos.real/ignore/g" build/ljs_parser.mly
	sed -i "s/Ljs_syntax/Interpreter/g" build/ljs_parser.mly
	sed -i "s/Ljs_syntax/Interpreter/g" build/ljs_lexer.mll
	sed -i "s/Prelude\.id/string/g" build/ljs_parser.mly

copy: coq caml/ copy_ljs
	mkdir -p build/
	cp coq/*.ml coq/*.mli build/
	cp caml/*.ml build/

native: copy
	cd build/; ocamlbuild eval.native

byte:copy
	cd build/; ocamlbuild eval.byte -tag debug

interpreter: native

snapshot:
	./build/eval.native envs/es5.env -save tests/es5.dump

tests: snapshot
	tests/run_tests.py tests/es5.dump

clean:
	make -C coq/ clean
	rm -f coq/*.ml coq/*.mli
	rm -rf build/*

.PHONY: coq caml clean tests
