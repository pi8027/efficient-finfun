# Program Extraction for Mutable Arrays

By Kazuhiko Sakaguchi

This repository provides a novel, lightweight, and axiom-free method for
verification and extraction of efficient effectful programs which use mutable
arrays. Our method consists of the following three parts:
- Improved Extraction Plugin for Coq (see `coq-mod` submodule)
- Modified Mathematical Components (MathComp) Library
  (see `math-comp-mod` submodule)
- Small Monadic DSL for Mutable Array Programming --- The Array State Monad
  (see `theories/marray/`)

## Requirements

* OPAM, OCaml 4.05.0+flambda, Camlp5, Ocamlbuild and ocamlfind
* tmux and zsh (for benchmark tools and build scripts)

Following materials are also required, but included as submodules or
automatically downloaded by the build script.

* Coq
  ([official version 8.7.0](https://github.com/coq/coq/tree/V8.7.0) and
   [extraction-efficient-finfun-master branch](https://github.com/pi8027/coq/tree/extraction-efficient-finfun-master))
* Mathematical Components Library
  ([official version 1.6.4](https://github.com/math-comp/math-comp/tree/mathcomp-1.6.4) and
   [modified-fintype branch](https://github.com/pi8027/math-comp/tree/modified-fintype))
* [Constructive Regular Language Library](http://www.ps.uni-saarland.de/~doczkal/regular/)
  (updated 2013-12-07, apply regular.patch)

## How to Build

    $ ./build-base
    Coq, MathComp and the regular language library will be rebuilt. Do you want to continue? [yes/no] YES
    ...
    $ ./build
    ...

## References

* Kazuhiko Sakaguchi and Yukiyoshi Kameyama.
  Efficient Finite-Domain Function Library for the Coq Proof Assistant.
  IPSJ Transactions on Programming, Vol 10, No 1, pp. 14-28, 2017.
* 坂口和彦 (2016)「Coq による定理証明 2016.12」 Tsukuba Coq Users' Group.
  ([web page](http://tcug.jp/books/2016-12/))
* 坂口和彦 (2015)「Coq による定理証明 2015.12」 Tsukuba Coq Users' Group.
  ([web page](http://tcug.jp/books/2015-12/))
