Require Import all_ssreflect all_algebra presburger.
Require Extraction.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Load "../extraction_common_dffun.v".

Extraction Inline fst snd.

(* range *)

Extraction Inline
  range_eqType range_eqMixin range_subType range_choiceType range_countType
  range_finType range_finMixin.


(* automata *)

Extraction Inline
  automata.dfa_state automata.dfa_s automata.dfa_fin automata.dfa_trans
  automata.dfa_lang
  automata.nfa_state automata.nfa_s automata.nfa_fin automata.nfa_trans
  automata.nfa_to_dfa automata.dfa_compl automata.dfa_op
  leq_dfa eq_dfa nfa_of_exists.

(* Avoid extractor bugs: type mismatch, assertion failure, etc. *)

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

Extraction Language Ocaml.
Set Extraction Flag 8175.

Extraction "../../ocaml/matrix_after.ml" matrix_mult_test finfun_app_test.

Extraction "../../ocaml/presburger_after.ml"
           bool_finType finfun_finType exp_finIndexType f_divisible
           presburger_dec presburger_st_dec presburger_sat presburger_valid.
