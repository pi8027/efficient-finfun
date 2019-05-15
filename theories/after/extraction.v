Require Import all_ssreflect all_algebra presburger.
Require Extraction.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Load "../extraction_common.v".

(* range *)

Extraction Inline
  range_eqType range_eqMixin range_subType range_choiceType range_countType
  range_finType range_finMixin.

(* finTypes *)

Extraction Inline
  fin_encode fin_decode
  Finite.mixin_base Finite.mixin_card Finite.mixin_enc Finite.mixin_dec
  Finite.base Finite.mixin Finite.base2 Finite.class Finite.clone
  Finite.EnumDef.enum Finite.card Finite.encode Finite.decode
  Finite.eqType Finite.choiceType Finite.countType
  prod_fin_encode prod_fin_decode finfun_fin_encode finfun_fin_decode.

(* automata *)

Extraction Inline
  automata.dfa_state automata.dfa_s automata.dfa_fin automata.dfa_trans
  automata.dfa_lang
  automata.nfa_state automata.nfa_s automata.nfa_fin automata.nfa_trans
  automata.nfa_to_dfa automata.dfa_compl automata.dfa_op
  leq_dfa eq_dfa nfa_of_exists.

(* avoiding extractor bugs: type mismatch, assertion failure, etc. *)

Extract Constant SetDef.pred_of_set =>
  "(Obj.magic (fun t a x -> tnth a (t.Finite.mixin.Finite.mixin_enc x)))".

(* matrix *)

Definition matrix_mult_test (n : nat) :=
  let mx := (\matrix_(i < n, j < n) (i%:Z + j%:Z))%R in
  (mx *m mx)%R.

Definition finfun_app_test (n : nat) :=
  let f := [ffun i : 'I_n => i] in
  \sum_i f i.

(******************************************************************************)

Extraction Language OCaml.
Set Extraction Flag 8175.

Extraction "../../ocaml/matrix_after.ml" matrix_mult_test finfun_app_test.

Extraction "../../ocaml/presburger_after.ml"
           bool_finType finfun_of_finType exp_finIndexType f_divisible
           presburger_dec presburger_st_dec presburger_sat presburger_valid.
