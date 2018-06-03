Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Indices for reflexive tactics *)

Inductive rindex : Type := rindex_L of rindex | rindex_C | rindex_R of rindex.

Notation "#L i" := (rindex_L i) (at level 75, right associativity).
Notation "#C" := rindex_C (at level 75, right associativity).
Notation "#R i" := (rindex_R i) (at level 75, right associativity).

Fixpoint eqrindex (x y : rindex) : bool :=
  match x, y with
    | rindex_L x', rindex_L y' => eqrindex x' y'
    | rindex_C, rindex_C => true
    | rindex_R x', rindex_R y' => eqrindex x' y'
    | _, _ => false
  end.

Lemma eqrindexP : Equality.axiom eqrindex.
Proof.
move => x y; apply: (iffP idP) => [| <-]; last by elim: x.
by elim: x y => [x IH | | x IH] [y | | y] //= /IH ->.
Qed.

Canonical rindex_eqMixin := EqMixin eqrindexP.
Canonical rindex_eqType := Eval hnf in EqType rindex rindex_eqMixin.

Fixpoint leq_rindex (x y : rindex) : bool :=
  match x, y with
    | rindex_L x', rindex_L y' => leq_rindex x' y'
    | rindex_R x', rindex_R y' => leq_rindex x' y'
    | rindex_L _, _ => true
    | rindex_C, rindex_L _ => false
    | rindex_C, _ => true
    | rindex_R _, _ => false
  end.

Lemma leq_rindex_refl : reflexive leq_rindex.
Proof. by elim. Qed.

Lemma leq_rindex_trans : transitive leq_rindex.
Proof. by elim => [x IH | | x IH] [y | | y] [z | | z] //=; apply IH. Qed.

Lemma leq_rindex_antisym (x y : rindex) :
  leq_rindex x y -> leq_rindex y x -> x = y.
Proof.
by elim: x y => [x IH | | x IH] [y | | y] //= *; f_equal; apply IH.
Qed.

Lemma leq_rindex_total (x y : rindex) : leq_rindex x y || leq_rindex y x.
Proof. by elim: x y => [x IH | | x IH] []. Qed.

Ltac myquate F X C NIL :=
  let C' := fresh "C" in set C' := C;
  let rec quote_fold n i :=
    fold (F i) in X;
    lazymatch n with
      | ?n'.+1 =>
        quote_fold n' (rindex_L i);
        quote_fold n' (rindex_R i)
      | _ => idtac
    end
  in
  let rec quote_pop fs f n :=
    lazymatch fs with
      | @nil _ =>
        let f := eval cbv beta in f in
        let n' := eval compute in n in
        clear F; pose F := f;
        quote_fold n' rindex_C
      | cons (?fl, ?xs', ?m') ?fstail =>
        quote_pop fstail
                  (fun i => match i with
                              | rindex_L i' => fl i'
                              | rindex_C => xs'
                              | rindex_R i' => f i'
                            end) (n + m').+1
    end
  in
  let rec quote_num fs :=
    lazymatch goal with
      | X := context [C ?xs] |- _ =>
        fold (C' xs) in X;
        lazymatch goal with
          | X := context [C ?ys] |- _ =>
            fold (C' ys) in X;
            quote_push fs (fun _ : rindex => xs) ys 0
          | _ => quote_pop fs (fun _ : rindex => xs) 1
        end
      | _ => quote_pop fs (fun _ : rindex => NIL) 1
    end
  with quote_push fs f xs n :=
    lazymatch fs with
      | @nil _ => quote_num [:: (f, xs, n)]
      | cons (?fl, ?xs', ?m.+1) ?fstail =>
        quote_num ((f, xs, n) :: (fl, xs', m) :: fstail)
      | cons (?fl, ?xs', _) ?fstail =>
        quote_push fstail
                   (fun i => match i with
                               | rindex_L i' => fl i'
                               | rindex_C => xs'
                               | rindex_R i' => f i'
                             end) xs (n.+1)
    end
  in
  lazymatch type of C with ?T -> ?EX =>
    quote_num (@nil ((rindex -> T) * T * nat)); subst C'
  end.
