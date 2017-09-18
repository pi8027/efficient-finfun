# Extraction of Efficient Programs Which Handle Mutable Arrays

By Kazuhiko Sakaguchi

This repository provides a new method to extract efficient programs
handling mutable arrays from Coq proofs, which consists of following
parts:
- Modified MathComp (Mathematical Components) Library
  (provided by the `math-comp-mod` submodule):

  In our method, `T`-indexed arrays of `A` (where `T` is a finite set)
  are represented as finite-domain functions (finfuns) from `T` to `A`
  which is provided by the MathComp library.
  The original MathComp library characterizes finite types (fintypes)
  by an enumeration of its elements, and it makes the construction and
  application of finfuns inefficient.  We make it efficiently
  computable by recharacterizing fintypes by a bijection to a finite
  ordinal type `'I_n`.
- Array State Monad:

  We define a specialized state monad called the "array state monad"
  for handling mutable arrays, which takes only arrays (finfuns) as
  states, and restricts access to states as if all states are mutable
  cells.
  In Coq programs, the array state monad is defined as an inductive
  data type, and its actions are interpreted as pure functions of type
  `S -> S * A` by the run function.
  By program extraction with replacements (`Extract Inductive` and
  `Extract Constant`) for some definitions, array state monad actions
  are translated to OCaml functions of type `S -> A` which propagate
  changes of state by mutation, and is efficiently computable.
- Modified Extraction Plugin for the Coq
  (provided by the `coq-mod` submodule):

  Array state monad actions constructed with case analysis inhibit
  inlining and increases the cost of function calls.
  For example, the following conversion is performed by program
  extraction and inlining:
  
      bind (get(i)) (fun x => if odd x then set(i, x+1) else set(i, x+2))
  
  ↓ Coq to OCaml conversion by the program extraction
  
      (fun f g s -> let r = f s in g r s)
        ((fun i s -> s.(i)) i)
        (fun x -> if odd x
                  then (fun i x s -> s.(i) <- x) i (x + 1)
	          else (fun i x s -> s.(i) <- x) i (x + 2))
  
  ↓ Inlining

      (fun s ->
       let r = s.(i) in
       (if odd r
        then (fun s -> s.(i) <- r + 1)
        else (fun s -> s.(i) <- r + 2)) s) .

  By using the fact that the condition `odd r` is a pure computation,
  the argument `s` of the conditional expression can be distributed to
  each branch.
  We built such a conversion into the program extraction plugin of the
  Coq by reason that the OCaml compiler cannot perform it.

## Requirements

* OPAM, OCaml 4.04.0+flambda, Camlp5, Ocamlbuild and ocamlfind
* tmux and zsh (for benchmark tools and build scripts)

Following materials are also required, but they are included as
submodules or automatically downloaded by the build script.

* Coq
  ([official version 8.6.1](https://github.com/coq/coq/tree/V8.6.1) and
   [extraction-lift-abs branch](https://github.com/pi8027/coq/tree/extraction-lift-abs))
* Mathematical Components Library
  ([official version 1.6.1](https://github.com/math-comp/math-comp/tree/mathcomp-1.6.1) and
   [modified-fintype branch](https://github.com/pi8027/math-comp/tree/modified-fintype))
* [Constructive Regular Language Library](http://www.ps.uni-saarland.de/~doczkal/regular/)
  (updated 2013-12-07, apply regular.patch)

## How to Build

    $ ./build_base
    Coq, MathComp and the regular language library will be rebuilt. Do you want to continue? [yes/no] YES
    ...
    $ ./build
    ...

<!--
## Using Benchmark Tool

    $ (cd ocaml; ZDOTDIR=. zsh)
    Presburger>> sat '(x; y; z) 2 <= x + y /\ x <= 2 /\ y <= 2 /\ x + y = 1 + 4 z'
-->

## References

* Kazuhiko Sakaguchi and Yukiyoshi Kameyama.
  Efficient Finite-Domain Function Library for the Coq Proof Assistant.
  IPSJ Transactions on Programming, Vol 10, No 1, pp. 14-28, 2017.
* 坂口和彦 (2016)「Coq による定理証明 2016.12」 Tsukuba Coq Users' Group.
  ([web page](http://tcug.jp/books/2016-12/))
* 坂口和彦 (2015)「Coq による定理証明 2015.12」 Tsukuba Coq Users' Group.
  ([web page](http://tcug.jp/books/2015-12/))
