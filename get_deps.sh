git submodule init
git submodule sync
git submodule update
cd jscert
make init
make || true
make

