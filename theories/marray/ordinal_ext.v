Require Import all_ssreflect Omega Psatz.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma fin_encode_inj (T : finType) : injective (@fin_encode T).
Proof. by apply/can_inj/fin_encodeK. Qed.

Lemma fin_decode_inj (T : finType) : injective (@fin_decode T).
Proof. by apply/can_inj/fin_decodeK. Qed.

(* nat *)

Definition predn' (n : nat) (H : 0 < n) := n.-1.

Definition subn' (n m : nat) (H : m <= n) := n - m.

Lemma ltnm0m (n m : nat) : n < m -> 0 < m.
Proof. by case: m. Qed.

(* Extended comparison predicates *)

Variant leq_xor_gtn' m n :
    bool -> bool -> bool -> bool ->
    nat -> nat -> nat -> nat -> nat -> nat -> Set :=
  | LeqNotGtn' of m <= n :
    leq_xor_gtn' m n (m < n) false true (n <= m) n n m m 0 (n - m)
  | GtnNotLeq' of n < m :
    leq_xor_gtn' m n false true false true m m n n (m - n) 0.

Lemma leqP' m n : leq_xor_gtn' m n
  (m < n) (n < m) (m <= n) (n <= m)
  (maxn m n) (maxn n m) (minn m n) (minn n m)
  (m - n) (n - m).
Proof.
rewrite (maxnC n) (minnC n); case: (leqP m n) => H.
- rewrite (maxn_idPr H) (minn_idPl H).
  by move: (H); rewrite -subn_eq0 => /eqP ->; constructor.
- rewrite (ltnW H) ltnNge leq_eqVlt H orbT
          (maxn_idPl (ltnW H)) (minn_idPr (ltnW H)).
  by move: (ltnW H); rewrite -subn_eq0 => /eqP ->; constructor.
Qed.

Variant compare_nat' m n :
    bool -> bool -> bool -> bool -> bool ->
    nat -> nat -> nat -> nat -> nat -> nat -> Set :=
  | CompareNatLt' of m < n :
    compare_nat' m n true false false true false n n m m 0 (n - m)
  | CompareNatGt' of m > n :
    compare_nat' m n false true false false true m m n n (m - n) 0
  | CompareNatEq' of m = n :
    compare_nat' m n false false true true true m m m m 0 0.

Lemma ltngtP' m n : compare_nat' m n
  (m < n) (n < m) (m == n) (m <= n) (n <= m)
  (maxn m n) (maxn n m) (minn m n) (minn n m)
  (m - n) (n - m).
Proof.
rewrite (maxnC n) (minnC n).
case: (ltngtP m n) => H; last by rewrite -H maxnn minnn subnn; constructor.
- rewrite (maxn_idPr (ltnW H)) (minn_idPl (ltnW H)).
  by move: (ltnW H); rewrite -subn_eq0 => /eqP ->; constructor.
- rewrite (maxn_idPl (ltnW H)) (minn_idPr (ltnW H)).
  by move: (ltnW H); rewrite -subn_eq0 => /eqP ->; constructor.
Qed.

(* ssromega *)

Module ssromega.

Inductive boolexpr :=
  | be_atom                of bool
  | be_true
  | be_false
  | be_and                 of boolexpr & boolexpr
  | be_or                  of boolexpr & boolexpr
  | be_impl                of boolexpr & boolexpr
  | be_xor                 of boolexpr & boolexpr
  | be_neg                 of boolexpr
  | be_leqn                of nat & nat
  | be_booleq              of boolexpr & boolexpr
  | be_ordeq (n : nat)     of 'I_n & 'I_n
  | be_polyeq (T : eqType) of T & T.

Fixpoint eval_boolexpr (e : boolexpr) : bool :=
  match e with
    | be_atom b => b
    | be_true => true
    | be_false => false
    | be_and el er => eval_boolexpr el && eval_boolexpr er
    | be_or el er => eval_boolexpr el || eval_boolexpr er
    | be_impl el er => eval_boolexpr el ==> eval_boolexpr er
    | be_xor el er => eval_boolexpr el (+) eval_boolexpr er
    | be_neg e => ~~ eval_boolexpr e
    | be_leqn n m => n <= m
    | be_booleq el er => eval_boolexpr el == eval_boolexpr er
    | be_ordeq _ i j => i == j
    | be_polyeq _ x y => x == y
  end.

Fixpoint denote_boolexpr (e : boolexpr) : Prop :=
  match e with
    | be_atom b => (0 < nat_of_bool b)%coq_nat
    | be_true => True
    | be_false => False
    | be_and el er => denote_boolexpr el /\ denote_boolexpr er
    | be_or el er => denote_boolexpr el \/ denote_boolexpr er
    | be_impl el er => denote_boolexpr el -> denote_boolexpr er
    | be_xor el er => ~ (denote_boolexpr el <-> denote_boolexpr er)
    | be_neg e => ~ denote_boolexpr e
    | be_leqn n m => (n <= m)%coq_nat
    | be_booleq el er => denote_boolexpr el <-> denote_boolexpr er
    | be_ordeq _ i j => nat_of_ord i = nat_of_ord j
    | be_polyeq _ x y => x = y
  end.

Definition denote_booleq (el er : boolexpr) : Prop :=
  match el, er with
  | be_true, _ => denote_boolexpr er
  | be_false, _ => ~ denote_boolexpr er
  | _, be_true => denote_boolexpr el
  | _, be_false => ~ denote_boolexpr el
  | _, _ => denote_boolexpr el <-> denote_boolexpr er
  end.

Lemma boolexprP (e : boolexpr) : reflect (denote_boolexpr e) (eval_boolexpr e).
Proof.
elim: e => /=;
  try by repeat (elim/Bool.reflect_rect || move=> ?); constructor; tauto.
- case; constructor=> /=; lia.
- exact: @leP.
- by move=> n i j; apply/(iffP eqP) => [| /ord_inj] ->.
- exact: @eqP.
Qed.

Lemma booleqP (el er : boolexpr) :
  eval_boolexpr el = eval_boolexpr er <-> denote_booleq el er.
Proof.
do 2 case: boolexprP; move=> H H0; split; case: el H H0; case: er => //=; tauto.
Qed.

Lemma ordP (n : nat) (i j : 'I_n) : i = j <-> nat_of_ord i = nat_of_ord j.
Proof. by split=> [| /ord_inj] ->. Qed.

Lemma maxE (m n : nat) : maxn m n = max m n.
Proof. rewrite/maxn; case: leqP => /leP; lia. Qed.

Lemma minE (m n : nat) : minn m n = min m n.
Proof. rewrite/minn; case: leqP => /leP; lia. Qed.

Ltac reify_boolexpr e :=
  lazymatch e with
    | true => be_true
    | false => be_false
    | ?el && ?er =>
      let el' := reify_boolexpr el in
      let er' := reify_boolexpr er in uconstr: (be_and el' er')
    | ?el || ?er =>
      let el' := reify_boolexpr el in
      let er' := reify_boolexpr er in uconstr: (be_or el' er')
    | ?el ==> ?er =>
      let el' := reify_boolexpr el in
      let er' := reify_boolexpr er in uconstr: (be_impl el' er')
    | ?el (+) ?er =>
      let el' := reify_boolexpr el in
      let er' := reify_boolexpr er in uconstr: (be_xor el' er')
    | ~~ ?e =>
      let e' := reify_boolexpr e in uconstr: (be_neg e')
    | ?n <= ?m => uconstr: (be_leqn n m)
    | _ =>
      match e with
        | @eq_op ?T ?el ?er (* bool *) =>
          let _ := constr: (erefl T : T = bool_eqType) in
          let el' := reify_boolexpr el in
          let er' := reify_boolexpr er in
          uconstr: (be_booleq el' er')
        | @eq_op ?T ?i ?j (* ordinal *) =>
          let _ := constr: (erefl T : T = ordinal_eqType _) in
          uconstr: (@be_ordeq _ i j)
        | @eq_op ?T ?x ?y => uconstr: (@be_polyeq T x y)
        | _ => uconstr: (be_atom e)
      end
  end.

Definition beq := @eq bool.

Ltac Propify :=
  unfold is_true, beq in *;
  repeat progress
    match goal with
      | H : context [@eq bool ?bl ?br] |- _ =>
        let el := reify_boolexpr bl in
        let er := reify_boolexpr br in
        (setoid_rewrite (booleqP el er) in H) ||
        (let H' := fresh in
         have H' := H;
         change (@eq bool) with beq in H;
         setoid_rewrite (booleqP el er) in H')
      | |- context [@eq bool ?bl ?br] =>
        let el := reify_boolexpr bl in
        let er := reify_boolexpr br in
        setoid_rewrite (booleqP el er)
      | H : context [@eq ('I_ _) ?i ?j] |- _ =>
        setoid_rewrite ordP in H
      | |- context [@eq ('I_ _) ?i ?j] =>
        setoid_rewrite ordP
    end;
  cbv [denote_booleq denote_boolexpr] in *.

Ltac natop_ssr2coq :=
  unfold predn', subn' in *;
  change addn with plus in *;
  change subn with minus in *;
  change muln with Init.Nat.mul in *;
  rewrite ?(maxE, minE);
  repeat lazymatch goal with
           | H : context [maxn _ _] |- _ => rewrite ?(maxE, minE) in H
           | H : context [minn _ _] |- _ => rewrite ?(maxE, minE) in H
         end.

Ltac ssromega :=
  move=> *; simpl in *; Propify; simpl in *; natop_ssr2coq; lia.

End ssromega.

Ltac ssromega := ssromega.ssromega.

(* test code for ssromega *)

Module ssromega_test.
Goal forall m n, minn (maxn m n) m = m. ssromega. Qed.
Goal forall m n, minn n (maxn m n) = n. ssromega. Qed.
Goal forall m n, maxn (minn m n) m = m. ssromega. Qed.
Goal forall m n, maxn n (minn m n) = n. ssromega. Qed.
Goal forall m n, maxn m n = m + (n - m). ssromega. Qed.
Goal forall m n, minn m n = m - (m - n). ssromega. Qed.
Goal forall m n, minn m n = m <-> m <= n. ssromega. Qed.
Goal forall m n, maxn m n = n <-> m <= n. ssromega. Qed.
Goal forall m n, maxn m n - minn m n = (m - n) + (n - m). ssromega. Qed.
Goal forall m n, minn m n - maxn m n = 0. ssromega. Qed.
Goal forall m n, minn m n + maxn m n = m + n. ssromega. Qed.
Goal forall m n, minn m n + (m - n) = m. ssromega. Qed.
Goal forall m n, maxn m n - (n - m) = m. ssromega. Qed.
End ssromega_test.

(* Ordinal *)

Lemma well_founded_ordgt (n : nat) : well_founded (fun i j : 'I_n => j < i).
Proof.
move=> i; elim: {3}n i (leq_addr i n) => [i | m IH i H];
  first by rewrite add0n => /(leq_trans (ltn_ord i)); rewrite ltnn.
by constructor=> j H0; apply/IH/(leq_trans H); rewrite addSnnS leq_add2l.
Qed.

Lemma well_founded_ordlt (n : nat) : well_founded (fun i j : 'I_n => i < j).
Proof.
move=> i; elim: {3}n i (ltn_ord i) => [// |] m IH i.
by rewrite ltnS => H; constructor=> j H0; apply/IH/(leq_trans H0).
Qed.

Definition lshift' (m n : nat) (i : 'I_n) : 'I_(m + n) :=
  @Ordinal (m + n) i (leq_trans (ltn_ord i) (leq_addl m n)).

Definition rshift' (m n : nat) (i : 'I_m) : 'I_(m + n) :=
  @Ordinal (m + n) (n + i) ltac:(by rewrite addnC ltn_add2r ltn_ord).

Definition ltnidx_l (n i : nat) (j : 'I_n.+1) (H : i < j) : 'I_n :=
  @Ordinal n i (leq_trans H (ltn_ord j)).

Definition ltnidx_ls (n i : nat) (j : 'I_n.+1) (H : i < j) : 'I_n.+1 :=
  @Ordinal n.+1 i.+1 (leq_trans H (ltn_ord j)).

Definition ltnidx_rp (n : nat) (j : 'I_n.+1) (H : 0 < j) : 'I_n :=
  @Ordinal n (@predn' j H) ltac:(by case: j H => -[]).

Definition ord_pred (n : nat) (i : 'I_n) : 'I_n :=
  @Ordinal n i.-1 ltac:(by case: i => -[] //= i /ltnW).

Definition ord_pred' (n : nat) (i : 'I_n) (H : 0 < i) : 'I_n :=
  @Ordinal n (@predn' i H) ltac:(by case: i H => -[] //= i /ltnW).
