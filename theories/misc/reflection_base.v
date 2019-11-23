Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Quote.
Section Quote.

Variable A : Type.

Inductive varmap : Type :=
  | Empty_vm : varmap
  | Node_vm : A -> varmap -> varmap -> varmap.

Inductive index : Set :=
  | Left_idx : index -> index
  | Right_idx : index -> index
  | End_idx : index.

Fixpoint varmap_find (default_value : A) (i : index) (v : varmap) : A :=
  match i, v with
  | End_idx, Node_vm x _ _ => x
  | Right_idx i1, Node_vm x v1 v2 => varmap_find default_value i1 v2
  | Left_idx i1, Node_vm x v1 v2 => varmap_find default_value i1 v1
  | _, _ => default_value
  end.

Fixpoint index_eq (n m : index) : bool :=
  match n, m with
  | End_idx, End_idx => true
  | Left_idx n', Left_idx m' => index_eq n' m'
  | Right_idx n', Right_idx m' => index_eq n' m'
  | _, _ => false
  end.

End Quote.
End Quote.
Import Quote.

Lemma eqindexP : Equality.axiom index_eq.
Proof.
move=> x y; apply: (iffP idP) => [|<-]; last by elim: x.
by elim: x y => [x IH|x IH|] [y|y|] //= /IH ->.
Qed.

Canonical index_eqMixin := EqMixin eqindexP.
Canonical index_eqType := Eval hnf in EqType index index_eqMixin.

Fixpoint leq_index (x y : index) : bool :=
  match x, y with
    | End_idx, _ | Left_idx _, Right_idx _ => true
    | Left_idx x', Left_idx y' | Right_idx x', Right_idx y' => leq_index x' y'
    | _, _ => false
  end.

Definition geq_index (x y : index) : bool := leq_index y x.

Lemma leq_index_refl : reflexive leq_index.
Proof. by elim. Qed.

Lemma leq_index_trans : transitive leq_index.
Proof. by elim=> [x IH | x IH |] [y | y |] [z | z |] //=; apply: IH. Qed.

Lemma leq_index_antisym (x y : index) :
  leq_index x y -> leq_index y x -> x = y.
Proof. by elim: x y => [x IH | x IH |] [y | y |] //= *; f_equal; apply: IH. Qed.

Lemma leq_index_total (x y : index) : leq_index x y || leq_index y x.
Proof. by elim: x y => [x IH | x IH |] []. Qed.

Notation Singleton_vm x := (Node_vm x (Empty_vm _) (Empty_vm _)).

Definition varmap_find'
           (A : Type) (default : A) (v : varmap A) (i : index) : A :=
  varmap_find default i v.

Ltac myquote term tag default :=
  let lk (* lookup *) := constr: (varmap_find' default) in
  let find_tag term :=
    lazymatch term with
    | context [tag ?x] => eval pattern (tag x) in term
    | _ => constr: (tt)
    end
  in
  let rec pop term :=
    lazymatch term with
    | (let _ := tt in ?term') => pop term'
    | (let f' := ?f in let _ := tt in @?F f') =>
      let term' := eval cbv beta in (let f' := f in F f') in
      pop term'
    | (let f := lk ?m1 in let g := lk ?m2 in @?F f g) =>
      let term' := eval cbv beta in
        (let f := lk (Node_vm default m1 m2) in
         F (fun i => f (Left_idx i)) (fun i => f (Right_idx i)))
      in
      pop term'
    | _ => constr: (term)
    end
  in
  let rec push term :=
    lazymatch find_tag term with
    | (fun x' => let f := lk ?m1 in let g := lk ?m2 in @?F x' f g) (tag ?x) =>
      let term' := eval cbv beta in
        (let f := lk (Node_vm x m1 m2) in
         F (f End_idx) (fun i => f (Left_idx i)) (fun i => f (Right_idx i)))
      in
      let term' := push term' in
      constr: (let _ := tt in term')
    | (fun x' => let f := lk ?m in let _ := tt in @?F x' f) (tag ?x) =>
      eval cbv beta in (let f := lk m in F (tag x) f)
    | _ => constr: (term)
    end
  in
  let rec quote_rec term :=
    lazymatch find_tag term with
    | (fun x' => @?F x') (tag ?x) =>
      let term' := eval cbv beta in
        (let f := lk (Singleton_vm x) in F (f End_idx)) in
      let term'' := push term' in
      quote_rec term''
    | _ => pop term
    end
  in
  quote_rec term.

Ltac myquote' term tag default atoms :=
  let lk (* lookup *) := constr: (varmap_find' default) in
  let rec pop term :=
    lazymatch term with
    | (let _ := tt in ?term') => pop term'
    | (let f' := ?f in let _ := tt in @?F f') =>
      let term' := eval cbv beta in (let f' := f in F f') in
      pop term'
    | (let f := lk ?m1 in let g := lk ?m2 in @?F f g) =>
      let term' := eval cbv beta in
        (let f := lk (Node_vm default m1 m2) in
         F (fun i => f (Left_idx i)) (fun i => f (Right_idx i)))
      in
      pop term'
    | _ => constr: (term)
    end
  in
  let rec push_aux term n :=
    lazymatch n with
    | ?n'.+1 => let term' := constr: (let _ := tt in term) in push_aux term' n'
    | 0 => term
    end
  in
  let rec push term atoms n :=
    lazymatch atoms with
    | ?atom :: ?atoms' =>
      lazymatch eval pattern (tag atom) in term with
      | (fun x' => let f := lk ?m1 in let g := lk ?m2 in @?F x' f g) _ =>
        let term' := eval cbv beta in
          (let f := lk (Node_vm atom m1 m2) in
           F (f End_idx) (fun i => f (Left_idx i)) (fun i => f (Right_idx i)))
        in
        push term' atoms' (n.+1)
      | (fun x' => let f := lk ?m in let _ := tt in @?F x' f) _ =>
        let term' := eval cbv beta in (let f := lk m in F (tag atom) f) in
        let term'' := push_aux term' n in
        quote_rec term'' atoms
      | _ =>
        let term' := push_aux term n in
        quote_rec term' atoms
      end
    | _ => pop term
    end
  with quote_rec term atoms :=
    lazymatch atoms with
    | ?atom :: ?atoms' =>
      lazymatch eval pattern (tag atom) in term with
      | (fun x' => @?F x') _ =>
        let term' := eval cbv beta in
          (let f := lk (Singleton_vm atom) in F (f End_idx)) in
        push term' atoms' 0
      end
    | _ => pop term
    end
  in
  quote_rec term atoms.
