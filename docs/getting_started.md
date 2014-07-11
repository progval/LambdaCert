# Getting started

This guide is for people new to LambdaJS/JSCert/LambdaCert.
We will start from a fresh Debian testing install.

We will install everything in the directory `~/js/`. So:

```
mkdir ~/js/
```


## Some reading

You can skip this section for now and come back while you will be waiting
for your dependencies to compile.



We will deal with three kinds of languages. The two first are obviously
Javascript and LambdaJS, but there are also LambdaJS environments.
(Actually, LambdaS5 deals with a few other languages: ExprJS (used as
an intermediate language while desugaring) and S5-CPS.)

Environments can be seen as a standard library for LambdaJS. They are
written in a LambdaJS-like language (they mostly share the same parser
code), and are evaluated before LambdaJS code, by the interpreter.
They provide all the features we need to run desugared Javascript code,
while keeping the interpreter very small.

The downside is they are quite long to run on slow machines/interpreters.
The original LambdaJS implementation (aka. LambdaS5) loads `es5.env`
(the main environment) in a few seconds, but my implementation in
LambdaCert takes two minutes.
In order to reduce that delay, both implementations provide “snapshots”,
ie. they evaluate the environment once and then dump the state of the
interpreter to a file.

As they are not needed with LambdaS5 I will not mention their usage,
but I will for LambdaCert.


## Installing everything we need

### Dependencies

On an up-to-date system, your default package manager and OPAM (the
OCaml package manager) should be ok:

```
sudo aptitude install autotools git subversion ocaml ocaml-native-compilers ocaml-findlib camlp4-extra opam coq coq-theories libcoq-ocaml m4 autoconf
OPAMYES=1 opam init
OPAMYES=1 opam install xml-light bisect
eval `opam config env`
```

You also have to install SpiderMonkey (LambdaS5 uses it for parsing
Javascript code). This bit is a bit tricky as SpiderMonkey is not
always packaged as a standalone executable.
Currently, this works on Debian testing:

```
sudo aptitude install libmozjs-24-bin
```


With Homebrew, the command to run is:

```
brew install spidermonkey
```


### Compiling LambdaS5

We will use a patched version of LambdaS5 (you can see my patches
[here](https://github.com/brownplt/LambdaS5/pulls/ProgVal) and
[here](https://github.com/brownplt/LambdaS5/pulls/ProgVal?state=closed))

First, get the source code (about 66MB):

```
cd ~/js/
git clone https://github.com/ProgVal/LambdaS5.git
cd LambdaS5/
git checkout working
```

Then, compile ocamlgraph:

```
cd src/ocamlgraph-1.8.1
autoreconf
./configure
make
cp graph.cmi graph.cma ../../lib/
```

Then, you can compile LambdaS5:

```
cd ..
make
cd ..
```

You now have to make LambdaS5 aware of a path where it can find SpiderMonkey.
If you installed `libmozjs24-bin`, you can use this command:

```
rm -f bin/js
ln -s `which js24` bin/js
```

Otherwise, you have to find your own way to do it.

You may also try to use a standalone SpiderMonkey executable provided with
LambdaS5, but you have to install its dependencies manually. If you want
to use it:

```
rm -f bin/js
ln -s js-24.6.0-Linux-x86_64 bin/js
```


### Compiling LambdaCert and JSCert

LambdaCert includes JSCert, so you need to compile to latter to compile
the former; and you can get both at once.

First, get the source code:

```
cd ~/js/
git clone https://github.com/ProgVal/LambdaCert.git
cd LambdaCert
```

Get JSCert and its dependencies and compile them (30MB to download, and
about ten minutes to compile):

```
./get_deps.sh
```

Note: this will checkout a subversion repository. If your ISP blocks
the subversion protocol, you can use HTTPS instead, by replacing
`svn checkout svn://scm.gforge.inria.fr/svn/tlc/trunk tlc` with
`echo "yes" | svn checkout --username anonsvn --password anonsvn https://scm.gforge.inria.fr/svn/tlc/trunk tlc`
in `jscert/Makefile` (and running `./get_deps.sh` again).

Compile LambdaCert’s LambdaS5 interpreter (about two minutes):

```
cd LambdaS5/
make
```


## Using what you just built

### LambdaS5

You can use it to run Javascript code:

```
cd ~/js/LambdaS5/
echo "print('Hello world')" > /tmp/hello.js
./obj/s5.d.byte -desugar /tmp/hello.js -env ./envs/es5.env -apply -eval
```

(If your SpiderMonkey setup is broken, you will get an error at this point.)



You can also use it to desugar Javascript code into LambdaJS code:

```
./obj/s5.d.byte -desugar /tmp/hello.js -print-src
```

And you can run LambdaJS code:

```
./obj/s5.d.byte -desugar /tmp/hello.js -print-src > /tmp/hello.ljs
./obj/s5.d.byte /tmp/hello.ljs -env envs/es5.env -apply -eval
```

### LambdaCert

For the moment, LambdaCert can only run LambdaJS code, so if you want to
run Javascript code, you first have to desugar it with LambdaS5:

```
cd ~/js/LambdaCert/LambdaS5/
~/js/LambdaS5/obj/s5.d.byte -desugar /tmp/hello.js -print-src > /tmp/hello.ljs
./build/eval.native envs/es5.env /tmp/hello.ljs
```

As mentionned at the beginning of this file, loading `es5.env` is long
(about two minutes on my machine).
So, if you want to run multiple LambdaJS files without having to wait
two minutes before it does anything useful, you can evaluate it once and
create snapshot; then use the snapshot for running LambdaJS code.

```
make snapshot
./build/eval.native -load tests/es5.dump /tmp/hello.ljs
./build/eval.native -load tests/es5.dump /tmp/hello.ljs
./build/eval.native -load tests/es5.dump /tmp/hello.ljs
```
