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

The simplest example:

```
./build/run.byte file.ljs
```


You can also use stdin:

```
echo "(func (foo, bar) { bar })('first', 'second')" | ./build/run.byte stdin
```


You can execute multiple files. The last one has to be a LambdaJS code file,
and all the previous ones have to be LambdaJS environment files.
For instance:

```
./build/run.byte ~/js/LambdaS5/envs/es5.env file.ljs
```


# How it works

## File hierarchy

Interpreter written mainly in Coq, in `LambdaS5/coq/*.v`

“Glue” files written in Caml, in `LambdaS5/caml/*.ml`. Also uses a
modified version of the original LambdaJS lexer and parser, in
`LambdaS5/caml/ljs/`.


## Code structure

TODO
