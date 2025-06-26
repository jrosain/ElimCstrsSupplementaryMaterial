# Elimination Constraints: Supplementary Material

This repository exposes some supplementary material for my master 2 internship
report featuring a modified version of Rocq.

## Installation

First, you need to follow the [installation instructions of Rocq](https://github.com/rocq-prover/rocq/blob/master/INSTALL.md).
Afterwards, you should be able to install and compile the files in this repository by using `./configure.sh`.

## Browsing the code

The recommended way of browsing the code is through emacs + proof general (the
following has been tested on commit `491857f`).
Be sure that the local variables are enabled, i.e., that `enable-local-variables` is set to `t`.
Then, add the following `.dir-locals.el` to the root of this repository:
```elisp
((coq-mode . ((coq-prog-name . "/path/to/this/directory/coq/_build/install/default/bin/coqtop")
              (coq-project-filename . "_RocqProject")
              (coq-compiler . "/path/to/this/directory/coq/_build/install/default/bin/coqc")
              (coq-prog-args . ("-Q" "/path/to/this/directory/coq/_build_ci/stdlib/_build/default/theories/" "Stdlib")))))
```
