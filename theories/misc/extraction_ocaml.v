Require Import all_ssreflect all_algebra.
Require Extraction.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Load "../extraction_common.v".

(* finTypes *)

Extraction Inline
  fin_encode fin_decode
  Finite.mixin_base Finite.mixin_card Finite.mixin_encode Finite.mixin_decode
  Finite.base Finite.mixin Finite.base2 Finite.class Finite.clone
  Finite.eqType Finite.choiceType Finite.countType Finite.raw_card
  prod_fin_encode prod_fin_decode finfun_fin_encode finfun_fin_decode.
