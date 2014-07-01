An attempt at writing certified stuff related to LambdaJS (LambdaJS
interpreter and JS => LambdaJS compiler)



# Usage

## Compiling

```
./get_deps.sh # Slow, you have to compile jscert (and thus Flocq and TLC)
cd LambdaS5
make
```

## Running the interpreter:

```
./build/run.byte < file.ljs
```


# How it works

## File hierarchy

Interpreter written mainly in Coq, in `LambdaS5/coq/*.v`

“Glue” files written in Caml, in `LambdaS5/caml/*.ml`. Also uses a
modified version of the original LambdaJS lexer and parser, in
`LambdaS5/caml/ljs/`.


## Code structure

TODO
