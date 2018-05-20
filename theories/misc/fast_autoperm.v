Require Import all_ssreflect all_algebra BinPos mergesort.
Import Mergesort_tailrec.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

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

Inductive Seq (A : Type) : Type :=
  | SeqEmbed of A
  | SeqNil
  | SeqCat   of Seq A & Seq A
  | SeqRev   of Seq A.

Fixpoint map_Seq (A B : Type) (f : A -> B) (xs : Seq A) : Seq B :=
  match xs with
    | SeqEmbed xs => SeqEmbed (f xs)
    | SeqNil => SeqNil _
    | SeqCat xs ys => SeqCat (map_Seq f xs) (map_Seq f ys)
    | SeqRev xs => SeqRev (map_Seq f xs)
  end.

Fixpoint denote_Seq (A Idx : Type) (f : Idx -> seq A) (xs : Seq Idx) : seq A :=
  match xs with
    | SeqEmbed xs => f xs
    | SeqNil => [::]
    | SeqCat xs ys => denote_Seq f xs ++ denote_Seq f ys
    | SeqRev xs => rev (denote_Seq f xs)
  end.

Lemma map_SeqE (A B : Type) (f : A -> B) :
  (forall i : A, SeqEmbed (f i) = map_Seq f (SeqEmbed i)) *
  (SeqNil B = map_Seq f (SeqNil A)) *
  (forall xs ys : Seq A, SeqCat (map_Seq f xs) (map_Seq f ys) =
                         map_Seq f (SeqCat xs ys)) *
  (forall xs : Seq A, SeqRev (map_Seq f xs) = map_Seq f (SeqRev xs)).
Proof. do !split. Qed.

Lemma denote_map_Seq (A Idx : Type) (f : Idx -> seq A) (xs : Seq Idx) :
  denote_Seq id (map_Seq f xs) = denote_Seq f xs.
Proof. elim: xs => //=; congruence. Qed.

Fixpoint sort_Seq_rec
         (xs : Seq rindex) (xss : seq (seq rindex)) : seq (seq rindex) :=
  match xs with
    | SeqEmbed i => merge_sort_push leq_rindex false [:: i] xss
    | SeqNil => xss
    | SeqCat xs ys => sort_Seq_rec ys (sort_Seq_rec xs xss)
    | SeqRev xs => sort_Seq_rec xs xss
  end.

Definition sort_Seq (xs : Seq rindex) : seq rindex :=
  merge_sort_pop leq_rindex false [::] (sort_Seq_rec xs [::]).

Lemma sort_Seq_perm (A : eqType) (f : rindex -> seq A) (xs : Seq rindex) :
  perm_eq (denote_Seq f xs) (flatten (map f (sort_Seq xs))).
Proof.
move: (merge_sort_pop_perm leq_rindex false [::] (sort_Seq_rec xs [::])).
rewrite /sort_Seq cat0s => /(perm_map f) /perm_flatten /perm_eqrP ->.
rewrite -[denote_Seq _ _]cats0 (_ : [::] = flatten (map f (flatten [::]))) //.
elim: xs [::] => [i | | xs IHx ys IHy | xs IH] xss //=;
  try by rewrite -?(perm_eqrP (IHy _)); autoperm.
move: (merge_sort_push_perm leq_rindex false [:: i] xss).
by rewrite cat1s => /(perm_map f) /perm_flatten /perm_eqrP ->.
Qed.

Lemma perm_eq_simpl (A : eqType) (f : rindex -> seq A) (xs ys : Seq rindex) :
  perm_eq (denote_Seq f xs) (denote_Seq f ys) =
  let (xs', ys') := perm_elim leq_rindex (sort_Seq xs) (sort_Seq ys) in
  perm_eq (flatten (map f xs')) (flatten (map f ys')).
Proof.
case: (perm_elim _ _ _) (perm_elim_perm leq_rindex (sort_Seq xs) (sort_Seq ys))
  => /= xs' ys' [].
rewrite (perm_eqlP (sort_Seq_perm _ _)) (perm_eqrP (sort_Seq_perm _ _)).
move => /(perm_map f) /perm_flatten /perm_eqlP ->
        /(perm_map f) /perm_flatten /perm_eqrP ->.
rewrite !map_cat !flatten_cat; autoperm.
Qed.

Ltac seqReify xs :=
  match xs with
    | @nil ?A => constr:(SeqNil A)
    | ?x :: ?xs =>
      let xs' := seqReify xs in constr:(SeqCat (SeqEmbed [:: x]) xs')
    | rcons ?xs ?x =>
      let xs' := seqReify xs in constr:(SeqCat xs' (SeqEmbed [:: x]))
    | ?xs ++ ?ys =>
      let xs' := seqReify xs in
      let ys' := seqReify ys in
      constr:(SeqCat xs' ys')
    | catrev ?xs ?ys =>
      let xs' := seqReify xs in
      let ys' := seqReify ys in
      constr:(SeqCat (SeqRev xs') ys')
    | rev ?xs => let xs' := seqReify xs in constr:(SeqRev xs')
    | _ => constr:(SeqEmbed xs)
  end.

Example ex1 (A : eqType) (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24 s25 s26 s27 s28 s29 s30 s31 s32 s33 s34 s35 s36 s37 s38 s39 s40 s41 s42 s43 s44 s45 s46 s47 s48 s49 s50 s51 s52 s53 s54 s55 s56 s57 s58 s59 s60 s61 s62 s63: seq A) :
  perm_eq ((((((s11 ++ s58) ++ (s4 ++ s23)) ++ ((s17 ++ (s35 ++ s26)) ++ (s50 ++ s56))) ++ (((s37 ++ s12) ++ ((s14 ++ s15) ++ (s16 ++ s13))) ++ ((s7 ++ (s46 ++ s41)) ++ (s6 ++ s19)))) ++ (((((s34 ++ s54) ++ s61) ++ s32) ++ (s38 ++ s5)) ++ (((s57 ++ s45) ++ s20) ++ ((s63 ++ s2) ++ s48)))) ++ (((((s18 ++ s25) ++ s39) ++ (((s49 ++ s27) ++ s44) ++ ((s40 ++ s60) ++ s55))) ++ (((s52 ++ s8) ++ (s59 ++ s22)) ++ (s24 ++ (s43 ++ s47)))) ++ ((((s0 ++ s36) ++ (s29 ++ s28)) ++ ((s3 ++ s62) ++ (s31 ++ s21))) ++ ((s1 ++ ((s30 ++ s10) ++ s42)) ++ ((s9 ++ s51) ++ (s33 ++ s53))))))
          ((((((s59 ++ s61) ++ s42) ++ ((s37 ++ s18) ++ s5)) ++ ((s2 ++ (s32 ++ s41)) ++ ((s1 ++ s16) ++ s17))) ++ (((((s54 ++ s47) ++ s62) ++ ((s49 ++ s38) ++ s23)) ++ ((s8 ++ s52) ++ (s19 ++ (s34 ++ s24)))) ++ ((((s36 ++ s27) ++ s21) ++ s7) ++ ((s30 ++ (s44 ++ s31)) ++ (s45 ++ s58))))) ++ (((((s28 ++ s0) ++ s51) ++ ((s60 ++ s48) ++ s63)) ++ (((s57 ++ s11) ++ ((s15 ++ s50) ++ s25)) ++ (((s26 ++ s13) ++ s29) ++ (s12 ++ s3)))) ++ ((((s9 ++ s4) ++ s10) ++ ((s53 ++ s6) ++ (s22 ++ s40))) ++ ((((s14 ++ s56) ++ s46) ++ (s55 ++ s35)) ++ ((s43 ++ s20) ++ (s39 ++ s33)))))).
Proof.
Time
let perm_eq' := fresh "perm_eq'" in pose perm_eq' := @perm_eq;
let SeqEmbed' := fresh "SeqEmbed'" in pose SeqEmbed' := @SeqEmbed;
let reify_permeq A peqs rewtac xs ys :=
  lazymatch goal with peqs : ?peqs_ |- _ =>
    let xs' := seqReify xs in
    let ys' := seqReify ys in
    let peq := constr: (perm_eq' _ (denote_Seq id xs') (denote_Seq id ys')) in
    let peq' := fresh "peq" in
    let Heq := fresh "H" in
    pose peq' := peq;
    (have Heq: perm_eq xs ys = peq' by rewrite /peq' /= -?cats1 ?catrevE);
    rewtac Heq;
    move: {Heq peqs} peq' (peqs, (erefl : peq' = peq)) => peq' peqs
  end
in
let reify_all A peqs :=
  repeat lazymatch goal with
    | |- context [@perm_eq A ?xs ?ys] =>
      let rewtac H := (rewrite H) in reify_permeq A peqs rewtac xs ys
    | H : context [@perm_eq A ?xs ?ys] |- _ =>
      let rewtac H' := (rewrite H' in H) in reify_permeq A peqs rewtac xs ys
    | x := context [@perm_eq A ?xs ?ys] |- _ =>
      let rewtac H := (rewrite H in x) in reify_permeq A peqs rewtac xs ys
  end
in
let rec autoperm_push peqs fs f xs :=
  lazymatch goal with
    | fs := @nil _ |- _ =>
      clear fs;
      set fs : seq (option ((rindex -> seq A) * seq A)) := [:: Some (f, xs)]
    | fs := cons None ?fstail |- _ =>
      clear fs;
      set fs := Some (f, xs) :: fstail
    | fs := cons (Some (?fl, ?xs')) ?fstail |- _ =>
      clear fs;
      let f' := fresh "f" in
      set f' : rindex -> seq A :=
        fun i => match i with
                   | rindex_L i' => fl i'
                   | rindex_C => xs'
                   | rindex_R i' => f i'
                 end;
      rewrite -!/(f' (rindex_L _)) -/(f' rindex_C) -!/(f' (rindex_R _))
        in peqs;
      unfold f, fl in f'; clear f fl;
      set fs := fstail;
      autoperm_push peqs fs f' xs;
      lazymatch goal with fs := ?fs' |- _ =>
        clear fs; set fs := None :: fs'
      end
  end
in
let rec autoperm_pop peqs fs fr :=
  lazymatch fs with
    | @nil _ => idtac
    | cons None ?fs' => autoperm_pop peqs fs' fr
    | cons (Some (?fl, ?xs)) ?fs' =>
      let fr' := fresh "f" in
      rename fr into fr';
      set fr : rindex -> seq A :=
        fun i => match i with
                   | rindex_L i' => fl i'
                   | rindex_C => xs
                   | rindex_R i' => fr' i'
                 end;
      rewrite -!/(fr (rindex_L _)) -/(fr rindex_C) -!/(fr (rindex_R _))
        in peqs;
      subst fl fr'; simpl in fr;
      autoperm_pop peqs fs' fr
  end
in
let autoperm_num A peqs f :=
  let fs := fresh "fs" in
  pose fs : seq (option ((rindex -> seq A) * seq A)) := [::];
  repeat lazymatch goal with
    | peqs : context [@SeqEmbed _ ?xs] |- _ =>
      rewrite -/(SeqEmbed' _ xs) in peqs;
      lazymatch goal with
        | peqs : context [@SeqEmbed _ ?ys] |- _ =>
          let f' := fresh "f" in
          pose f' : rindex -> seq A := fun _ => xs;
          rewrite -/(SeqEmbed' _ ys) -/(f' rindex_C) in peqs;
          autoperm_push peqs fs f' ys
      end
  end;
  lazymatch goal with fs := ?fs' |- _ =>
    clear f;
    lazymatch goal with
      | peqs : context [@SeqEmbed _ ?xs] |- _ =>
        pose f : rindex -> seq A := fun _ => xs;
        rewrite -/(f rindex_C) in peqs
      | _ => pose f : rindex -> seq A := fun _ => [::]
    end;
    clear fs; autoperm_pop peqs fs' f;
    rewrite /SeqEmbed' /perm_eq' !(map_SeqE f) !denote_map_Seq in peqs
  end
in
let do_autoperm A peqs :=
  reify_all A peqs;
  let f := fresh "f" in
  have f := tt;
  autoperm_num A peqs f;
  rewrite !perm_eq_simpl in peqs;
  repeat
    (let pe := fresh "pe" in set pe := perm_elim _ _ _ in peqs;
     native_compute in pe; subst pe);
  cbv iota beta in peqs
in
let peqs := fresh "peqs" in have peqs : unit := tt;
lazymatch goal with
  | [|- context [@perm_eq ?A ?xs ?ys]] => do_autoperm A peqs
  | H : context [@perm_eq ?A ?xs ?ys] |- _ => do_autoperm A peqs
  | x := context [@perm_eq ?A ?xs ?ys] |- _ => do_autoperm A peqs
end.
(********)
case: peqs => _ H; subst peq f => /=.
done.
Qed.