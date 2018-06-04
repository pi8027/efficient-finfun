Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(*******************************************************************************
 An efficient construction technique for balanced binary trees from lists:
 - This method can preserves the order of elements, and
 - All recursions used in this methods are structural.
*******************************************************************************)

(* Implementation 1: for binary trees with labeled leaves *)

Inductive tree (A : Type) := tbin of tree A & tree A | tsingle of A.

Module Construction_1.

Section Definitions.

Variable (A : Type).

Fixpoint push (t : tree A) (ts : seq (option (tree A))) :
  seq (option (tree A)) :=
  match ts with
    | [::] as ts' | None :: ts' => Some t :: ts'
    | Some t' :: ts' => None :: push (tbin t' t) ts'
  end.

Fixpoint pop (t : tree A) (ts : seq (option (tree A))) : tree A :=
  match ts with
    | [::] => t
    | None :: ts' => pop t ts'
    | Some t' :: ts' => pop (tbin t' t) ts'
  end.

Fixpoint rep_push (ts : seq (option (tree A))) (xs : seq A) (x : A) :
  tree A :=
  match xs with
    | [::] => pop (tsingle x) ts
    | x' :: xs' => rep_push (push (tsingle x) ts) xs' x'
  end.

Definition construct (xs : seq A) : option (tree A) :=
  match xs with
    | [::] => None
    | x :: xs => Some (rep_push [::] xs x)
  end.

End Definitions.

Notation "#< x >" := (tsingle x) (at level 75).
Notation "l ## r" := (tbin l r) (at level 75, no associativity).

Eval compute in (construct (iota 0 30)).
Eval compute in (construct (iota 0 31)).
Eval compute in (construct (iota 0 32)).
Eval compute in (construct (iota 0 33)).
Eval compute in (construct (iota 0 34)).

End Construction_1.


(* Implementation 2: for binary trees with labeled nodes *)

Inductive tree' (A : Type) := tnode of tree' A & A & tree' A | tnil.

Arguments tnil {A}.

Module Construction_2.

Section Definitions.

Variable (A : Type).

Fixpoint push (t : tree' A) (x : A) (ts : seq (option (tree' A * A))) :
  seq (option (tree' A * A)) :=
  match ts with
    | [::] as ts' | None :: ts' => Some (t, x) :: ts'
    | Some (t', x') :: ts' => None :: push (tnode t' x' t) x ts'
  end.

Fixpoint pop (t : tree' A) (ts : seq (option (tree' A * A))) : tree' A :=
  match ts with
    | [::] => t
    | None :: ts' => pop t ts'
    | Some (t', x') :: ts' => pop (tnode t' x' t) ts'
  end.

Fixpoint rep_push (ts : seq (option (tree' A * A))) (xs : seq A) : tree' A :=
  match xs with
    | [::] => pop tnil ts
    | [:: x] => pop (tnode tnil x tnil) ts
    | x :: x' :: xs' => rep_push (push (tnode tnil x tnil) x' ts) xs'
  end.

Definition construct (xs : seq A) : tree' A := rep_push [::] xs.

End Definitions.

Notation "l #< x ># r" := (tnode l x r) (at level 75, no associativity).

Eval compute in (construct (iota 0 29)).
Eval compute in (construct (iota 0 30)).
Eval compute in (construct (iota 0 31)).
Eval compute in (construct (iota 0 32)).
Eval compute in (construct (iota 0 33)).

End Construction_2.
