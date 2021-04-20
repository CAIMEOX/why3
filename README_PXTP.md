This branch, `cert_pxtp`, contains the source code corresponding to the article:
A framework for proof-carrying logical transformations.

Compilation
-----------

We show instructions to compile Why3 et and test the plugin for the checked
logical transformations. You will need a recent version of OCaml.

At the root of the project:
```shell
autoconf
./configure --enable-local
make -j
```

At this stage, you can call the binary executable file by `bin/why3`.

To be able to use Why3 completely, it is recommended that you install at least
Z3, CVC4 and Alt-Ergo.

In any case, do:
```shell
bin/why3 config --detect
```

To use the Lambdapi-checked transformations, you should have `lambdapi` in your
PATH. To that end, follow the instructions from the [project
repository](https://github.com/Deducteam/lambdapi).


Usage
-----

Checked transformations are available inside Why3 when invoking the `--cert` option.
They come with the following naming conventions:
  - OCaml-checked transformations end with `_ccert`.
  - Lambdapi-checked transformations end with `_lcert`.

In this way, to know which checked transformations are available, simply type
`_ccert` or `_dcert` in Why3's prompt.


Run the IDE on test files. For example, do one of the following:
```shell
bin/why3 ide --cert plugins/cert/tests/core
bin/why3 ide --cert plugins/cert/tests/rewrite
bin/why3 ide --cert plugins/cert/tests/induction
```
This can take a few seconds depending on the file this is loading.

Source code
-----------

The soure code is available in the directory `plugin/cert` and is mostly composed of the following files:
   - file `cert_syntax.ml` defines the representation of terms, types and tasks
   - file `cert_abstract.ml` implements the translation of Why3's tasks into this representation
   - file `cert_certificates.ml` defines the certificates and implements the elaboration
   - file `cert_trans_util.ml` defines utility functions for defining certifying transformations
   - file `cert_trans_core.ml` defines the core certifying transformations
   - file `cert_rewrite.ml` defines the certifying version of the `rewrite` transformation
   - file `cert_induction.ml` defines the certifying version of the `induction` transformation
   - file `cert_split.ml` defines the certifying version of the `split` transformation
   - file `cert_verif_caml.ml` implements the OCaml checker
   - file `cert_verif_lambdapi.ml` implements the Lambdapi checker
   - file `cert_register.ml`, given a checker, makes certifying transformations available as
     checked transformations inside Why3

In addition, the file `share/lambdapi/preamble.lp` defines the CoC encoding and
Lambdapi terms corresponding to certificate rules. It is used as a preamble to
the type checking problem.
