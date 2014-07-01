all: configure coq interpreter

configure: coq/configure coq/*.v
	cd coq;	./configure

coq: configure
	make -C coq/

copy_ljs:
	mkdir -p build/
	cp caml/ljs/*.ml{y,l} build/

edit_ljs:
	# You might want the following commands if you want to use the latest
	# version of LambdaJS' files. They are not enough to make the files
	# compatible with our implementation, but they help a lot.
	sed -i "s/open Prelude/(* open Prelude *)/" build/ljs_{parser.mly,lexer.mll}
	sed -i "s/Pos.real/ignore/g" build/ljs_parser.mly
	sed -i "s/Ljs_syntax/Interpreter/g" build/ljs_parser.mly
	sed -i "s/Ljs_syntax/Interpreter/g" build/ljs_lexer.mll
	sed -i "s/Prelude\.id/string/g" build/ljs_parser.mly

caml: coq caml/ copy_ljs
	mkdir -p build/
	cp coq/*.ml{,i} build/
	cp caml/*.ml build/
	cd build/; ocamlbuild run.byte -tag debug

interpreter: caml

clean:
	make -C coq/ clean
	rm -f coq/*.ml{i,}
	rm -rf build/*

.PHONY: coq caml clean
