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
echo "(func (foo, bar) { bar })('first', 'second')" | ./build/eval.native stdin
```


You can execute multiple files. The last one has to be a LambdaJS code file,
and all the previous ones have to be LambdaJS environment files.
For instance:

```
./build/eval.native ~/js/LambdaS5/envs/es5.env file.ljs
```

The previous command can be very long (two minutes on my machine), because it
has to evaluate the env file, which is rather big.

A faster way, if you have to run multiple files, is to evaluate it once, and
dump it. Thus, you only have to load the dump on each run:

```
./build/eval.native ~/js/LambdaS5/envs/es5.env -save /tmp/store.dump
./build/eval.native -load /tmp/store.dump foo.ljs
./build/eval.native -load /tmp/store.dump bar.ljs
```

This dump uses Caml's Marshal module, with the Closure flag (because we want
to dump TLC's LibStream's streams), so you should load the dump with the
exact same version of `eval.native` as the one used to save it. (You would
get a Marshal error otherwise.)

# How it works

## File hierarchy

Interpreter written mainly in Coq, in `LambdaS5/coq/*.v`

“Glue” files written in Caml, in `LambdaS5/caml/*.ml`. Also uses a
modified version of the original LambdaJS lexer and parser, in
`LambdaS5/caml/ljs/`.


## Code structure

TODO
