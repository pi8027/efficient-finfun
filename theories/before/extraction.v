From mathcomp Require Import all_ssreflect all_algebra.
Require Import presburger.
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
  Finite.mixin_base Finite.mixin_enum Finite.base Finite.mixin Finite.base2
  Finite.class Finite.clone Finite.eqType Finite.choiceType Finite.countType.

(* automata *)

Extraction Inline
  automata.dfa_state automata.dfa_s automata.dfa_fin automata.dfa_trans
  automata.dfa_lang
  automata.nfa_state automata.nfa_s automata.nfa_fin automata.nfa_trans
  automata.nfa_to_dfa automata.dfa_compl automata.dfa_op
  leq_dfa eq_dfa nfa_of_exists.

(* avoiding extractor bugs: type mismatch, assertion failure, etc. *)

Extract Constant SetDef.pred_of_set =>
  "(Obj.magic (fun t a x -> tnth a (Obj.magic enum_rank t x)))".

(* matrix *)

Definition matrix_mult_test (n : nat) :=
  let mx := (\matrix_(i < n, j < n) (i%:Z + j%:Z))%R in
  (mx *m mx)%R.

Definition finfun_app_test (n : nat) :=
  let f := [ffun i : 'I_n => i] in
  \sum_i f i.

(******************************************************************************)

Unset Extraction SafeImplicits.
Extraction Language Ocaml.
Set Extraction Flag 2031.

Extraction "../../ocaml/matrix_before.ml" matrix_mult_test finfun_app_test.

Extraction "../../ocaml/presburger_before.ml"
           bool_finType finfun_of_finType exp_finIndexType f_divisible
           presburger_dec presburger_st_dec presburger_sat presburger_valid.
