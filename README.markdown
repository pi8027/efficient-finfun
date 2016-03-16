# A Formalization of the Presburger Arithmetic in Coq/SSReflect

By Kazuhiko Sakaguchi

## Requirements

* Coq 8.5beta3 (official release of Coq 8.5 contains bug related to extraction)
  * Mathematical Components Library ([official version 1.6](http://math-comp.github.io/math-comp/) and [modified-fintype branch](https://github.com/pi8027/math-comp/tree/modified-fintype))
  * [Constructive Regular Language Library](http://www.ps.uni-saarland.de/~doczkal/regular/) (updated 2013-12-07, apply regular.patch)
* OCaml
* tmux and zsh (for benchmark tool)

## Build

Presburger 算術の形式化は、オリジナルの MathComp ライブラリと modified-fintype ブランチそれぞれに合わせて2種類用意した。前者は before/ 以下にあり、後者は after/ 以下にある。正規言語ライブラリはそれぞれについて使う MathComp ライブラリを差し替えてビルドし直す必要がある。使うライブラリのパスは、before/, after/ それぞれの下にあるファイル build の COQLIB= で開始する行に記述する。また、Proof General を用いて Coq のファイルを編集する場合には \_CoqProject ファイルも編集すると良いだろう。ベンチマーク用のファイルも含めて全てをビルドするには以下の手順を踏む。

    $ (cd before; ./build)
    $ (cd after; ./build)
    $ (cd ocaml; ./build)

## Using Benchmark Tool

    $ (cd ocaml; ZDOTDIR=. zsh)
    Presburger>> sat '(x; y; z) 2 <= x + y /\ x <= 2 /\ y <= 2 /\ x + y = 1 + 4 z'

## References

* 坂口和彦 (2015)「Coq による定理証明 2015.12」 Tsukuba Coq Users' Group. ([web page](http://tcug.jp/books/2015-12/))
* 坂口和彦, 亀山幸義「Coq/SSReflect の extraction の改善」(PPL2016 カテゴリ3). ([poster](http://logic.cs.tsukuba.ac.jp/~sakaguchi/posters/ppl2016.pdf))
