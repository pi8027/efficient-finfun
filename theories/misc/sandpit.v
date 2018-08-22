Require Import ssreflect ssrbool.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Inductive Bool :=
  | BoolT
  | BoolF
  | BoolAnd   of Bool & Bool
  | BoolOr    of Bool & Bool
  | BoolImply of Bool & Bool.

Fixpoint eval_Bool (e : Bool) : bool :=
  match e with
    | BoolT => true
    | BoolF => false
    | BoolAnd el er => eval_Bool el && eval_Bool er
    | BoolOr el er => eval_Bool el || eval_Bool er
    | BoolImply el er => eval_Bool el ==> eval_Bool er
  end.

Fixpoint denote_Bool (e : Bool) : Prop :=
  match e with
    | BoolT => True
    | BoolF => False
    | BoolAnd el er => denote_Bool el /\ denote_Bool er
    | BoolOr el er => denote_Bool el \/ denote_Bool er
    | BoolImply el er => denote_Bool el -> denote_Bool er
  end.

Lemma BoolP (e : Bool) : reflect (denote_Bool e) (eval_Bool e).
Proof.
elim: e => [| | el IHl er IHr | el IHl er IHr | el IHl er IHr];
  apply (iffP idP) => //=.
- by case/andP => /IHl Hl /IHr Hr.
- by case=> /IHl -> /IHr.
- by case/orP => [/IHl | /IHr] H; [left | right].
- by case=> [/IHl | /IHr] -> //=; rewrite orbT.
- by move/implyP => H /IHl /H /IHr.
- by move=> H; apply/implyP => /IHl /H /IHr.
Qed.

Lemma elim_Prop (e : Bool) : eval_Bool e -> denote_Bool e.
Proof. exact: (elimT (BoolP e)). Qed.

Ltac reify_Prop e :=
  lazymatch e with
    | True => constr: (BoolT)
    | False => constr: (BoolF)
    | ~ ?e =>
      let e' := reify_Prop e in
      constr: (BoolImply e' BoolF)
    | ?el /\ ?er =>
      let el' := reify_Prop el in
      let er' := reify_Prop er in
      constr: (BoolAnd el' er')
    | ?el \/ ?er =>
      let el' := reify_Prop el in
      let er' := reify_Prop er in
      constr: (BoolOr el' er')
    | ?el -> ?er =>
      let el' := reify_Prop el in
      let er' := reify_Prop er in
      constr: (BoolImply el' er')
  end.

(******************************************************************************)

Example ex1 : ((((((False -> False) -> False) -> False)
                 -> False) -> False) -> False) -> False.
Proof.
intro H.
apply H.
clear H.
repeat (intro H; apply H; clear H).
Defined.

Example ex1_tauto : ((((((False -> False) -> False) -> False)
                       -> False) -> False) -> False) -> False.
Proof.
tauto. (* is a tactic for proving propositional tautologies. *)
Defined.

Example ex1_refl : ((((((False -> False) -> False) -> False)
                      -> False) -> False) -> False) -> False.
Proof.
match goal with |- ?P =>
  let e := reify_Prop P in apply (@elim_Prop e)
end.
vm_compute.
reflexivity.
Defined.

Print ex1.
Print ex1_tauto.
Print ex1_refl.

(******************************************************************************)

Fixpoint gen_long_tautology (n : nat) : Prop :=
  (if n is S n' then gen_long_tautology n' -> False else False) -> False.

Example ex2 : gen_long_tautology 2000.
Proof.
simpl.
Fail timeout 10 tauto.
Time repeat apply. (* Finished transaction in 2.516 secs (2.5u,0.015s) (successful) *)
Time Defined. (* Finished transaction in 8.47 secs (8.469u,0.s) (successful) *)

Example ex2_refl : gen_long_tautology 2000.
Proof.
simpl.
Time
match goal with |- ?P =>
  let e := reify_Prop P in exact: (@elim_Prop e (eq_refl _))
end. (* Finished transaction in 0.469 secs (0.465u,0.003s) (successful) *)
Time Qed. (* Finished transaction in 0.057 secs (0.057u,0.s) (successful) *)
