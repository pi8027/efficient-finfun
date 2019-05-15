Require Import all_ssreflect all_algebra.
Require Extraction.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Load "../extraction_common.v".

(* finTypes *)

Extraction Inline
  fin_encode fin_decode
  Finite.mixin_base Finite.mixin_card Finite.mixin_enc Finite.mixin_dec
  Finite.base Finite.mixin Finite.base2 Finite.class Finite.clone
  Finite.EnumDef.enum Finite.card Finite.encode Finite.decode
  Finite.eqType Finite.choiceType Finite.countType
  prod_fin_encode prod_fin_decode finfun_fin_encode finfun_fin_decode.
