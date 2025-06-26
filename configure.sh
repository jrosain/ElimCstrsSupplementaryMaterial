#!/bin/bash

git submodule init
git submodule update --remote

cd coq && make world && make ci-stdlib
cd ..

rocq=$(pwd)/coq/_build/install/default/bin/rocq
$rocq makefile -f _RocqProject -o RocqMakefile -docroot theories

(cat coqdocjs/Makefile.doc | sed 's/Makefile.coq/RocqMakefile/') >> RocqMakefile

export OCAMLPATH=$(pwd)/coq/_build/install/default/lib/
export ROCQLIB=$(pwd)/coq/_build/default

make -f RocqMakefile
