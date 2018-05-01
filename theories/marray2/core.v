Require Import all_ssreflect fingroup perm.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(******************************************************************************)
(* General framework for mutable array programming                            *)
(******************************************************************************)

(* copyType: provides a method for deep copying of states. *)

Inductive copyable : Type -> Type :=
  | copyable_ffun (I : finType) (T : Type) : copyable {ffun I -> T}
  | copyable_prod (T T' : Type) :
    copyable T -> copyable T' -> copyable (T * T').

Definition copy_ffun (I : finType) (T : Type) (f : {ffun I -> T}) := f.

Definition copy_raw : forall T, copyable T -> T -> T :=
  @copyable_rect
    (fun T _ => T -> T)
    (fun (I : finType) T (f : {ffun I -> T}) => copy_ffun f)
    (fun T T' _ cT _ cT' '(x, y) => (cT x, cT' y)).

Module Copyable.

Structure type : Type := Pack { sort; _ : copyable sort }.

Section ClassDef.
Variable (T : Type) (cT : type).

Definition class :=
  let: Pack _ c := cT return copyable (sort cT) in c.
Definition pack c := @Pack T c.
Definition clone := fun c & sort cT -> T & phant_id (pack c) cT => pack c.

End ClassDef.

Module Exports.

Coercion sort : type >-> Sortclass.

Notation copyType := type.
Notation "[ 'copyMixin' 'of' T ]" :=
  (class _ : copyable T)
    (at level 0, format "[ 'copyMixin' 'of' T ]") : form_scope.
Notation "[ 'copyType' 'of' T ]" :=
  (@clone T _ _ idfun id).

End Exports.

End Copyable.

Import Copyable.Exports.

Definition copy (T : copyType) : T -> T := copy_raw (Copyable.class T).

Lemma copyE (T : copyType) (x : T) : copy x = x.
Proof.
by rewrite /copy;
  elim: (Copyable.class T) x => //= Tl Tr cl Hl cr Hr [x y]; rewrite Hl Hr.
Qed.

Canonical finfun_copyType (I : finType) (T : Type) : copyType :=
  @Copyable.Pack {ffun I -> T} (copyable_ffun I T).

Canonical prod_copyType (T1 T2 : copyType) : copyType :=
  @Copyable.Pack
    (T1 * T2) (copyable_prod (Copyable.class T1) (Copyable.class T2)).

Global Opaque copy_raw copy.

(*
Module Type CopyableRawSig.

Parameters
  (mixin_of : Type -> Type)
  (copy : forall (T : Type), mixin_of T -> T -> T)
  (copyE : forall (T : Type) (C : mixin_of T) (x : T), copy C x = x)
  (ffun_mixin : forall (I : finType) (T : Type), mixin_of {ffun I -> T})
  (pair_mixin :
     forall (T1 T2 : Type) (C1 : mixin_of T1) (C2 : mixin_of T2),
       mixin_of (T1 * T2)).

End CopyableRawSig.

Module CopyableRaw : CopyableRawSig.

Record mixin_of_ (T : Type) : Type :=
  Mixin { copy_ : T -> T; copyE_ : forall x, copy_ x = x }.
Definition mixin_of := mixin_of_.
Definition copy := copy_.

Lemma copyE (T : Type) (C : mixin_of T) (x : T) : copy C x = x.
Proof. by case: C => /= copy ->. Qed.

Definition ffun_copy
           (I : finType) (T : Type) (f : {ffun I -> T}) : {ffun I -> T} := f.

Definition ffun_mixin (I : finType) (T : Type) : mixin_of {ffun I -> T} :=
  @Mixin _ (@ffun_copy I T) (fun _ => erefl).

Lemma pair_mixin_subproof
      (T1 T2 : Type) (C1 : mixin_of T1) (C2 : mixin_of T2) (x : T1 * T2) :
  (let (x, y) := x in (copy C1 x, copy C2 y)) = x.
Proof. by case: x => x y; rewrite !copyE. Qed.

Definition pair_mixin (T1 T2 : Type) (C1 : mixin_of T1) (C2 : mixin_of T2) :
  mixin_of (T1 * T2) :=
  @Mixin (T1 * T2) (fun '(x, y) => (copy C1 x, copy C2 y))
         (pair_mixin_subproof C1 C2).

End CopyableRaw.

Module Copyable.

Structure type : Type := Pack { sort; _ : CopyableRaw.mixin_of sort }.

Section ClassDef.
Variable (T : Type) (cT : type).

Definition class :=
  let: Pack _ c := cT return CopyableRaw.mixin_of (sort cT) in c.
Definition pack c := @Pack T c.
Definition clone := fun c & sort cT -> T & phant_id (pack c) cT => pack c.

End ClassDef.

Module Exports.

Coercion sort : type >-> Sortclass.

Notation copyType := type.
Notation "[ 'copyMixin' 'of' T ]" :=
  (class _ : CopyableRaw.mixin_of T)
    (at level 0, format "[ 'copyMixin' 'of' T ]") : form_scope.
Notation "[ 'copyType' 'of' T ]" :=
  (@clone T _ _ idfun id).

End Exports.

End Copyable.

Import Copyable.Exports.

Definition copy (T : copyType) : T -> T := CopyableRaw.copy (Copyable.class T).

Lemma copyE (T : copyType) (x : T) : copy x = x.
Proof. by rewrite /copy; case: T x => /= T m x; rewrite CopyableRaw.copyE. Qed.

Canonical finfun_copyType (I : finType) (T : Type) : copyType :=
  @Copyable.Pack {ffun I -> T} (CopyableRaw.ffun_mixin I T).

Canonical pair_copyType (T1 T2 : copyType) : copyType :=
  @Copyable.Pack
    (T1 * T2) (CopyableRaw.pair_mixin (Copyable.class T1) (Copyable.class T2)).
*)

(*
 The array state monad
 [Note] AState_rect and run_AState_raw must not be called from other than
 run_AState. This restriction can be enforced by hiding some definitions by
 using a modules and module type, but "Extract Constant" command can't be used
 for hidden definitions.
*)

Definition ffun_set
           (I : finType) (T : Type) (i : I) (x : T) (f : {ffun I -> T}) :=
  [ffun j => if j == i then x else f j].

Lemma subst_id (I : finType) (T : Type) (i : I) (x : T) (f : {ffun I -> T}) :
  x = f i -> ffun_set i x f = f.
Proof. by move ->; apply/ffunP => j; rewrite ffunE; case: eqP => // ->. Qed.

Inductive AState : Type -> Type -> Type -> Type :=
  | astate_ret_ (S A : Type) : A -> AState S S A
  | astate_bind_ (S S' S'' A B : Type) :
      AState S S' A -> (A -> AState S' S'' B) -> AState S S'' B
  | astate_frameL_ (Sl Sl' Sr A : Type) :
      AState Sl Sl' A -> AState (Sl * Sr) (Sl' * Sr) A
  | astate_frameR_ (Sl Sr Sr' A : Type) :
      AState Sr Sr' A -> AState (Sl * Sr) (Sl * Sr') A
  | astate_A_ (S S' S'' : Type) : AState ((S * S') * S'') (S * (S' * S'')) unit
  | astate_A'_ (S S' S'' : Type) : AState (S * (S' * S'')) ((S * S') * S'') unit
  | astate_C_ (S S' : Type) : AState (S * S') (S' * S) unit
  | astate_GET_ (I : finType) (T : Type) :
      'I_#|I| -> AState {ffun I -> T} {ffun I -> T} T
  | astate_SET_ (I : finType) (T : Type) :
      'I_#|I| -> T -> AState {ffun I -> T} {ffun I -> T} unit.

Definition astate_ret {S A} a := @astate_ret_ S A a.
Definition astate_bind {S S' S'' A B} := @astate_bind_ S S' S'' A B.
Definition astate_frameL {Sl Sl' Sr A} := @astate_frameL_ Sl Sl' Sr A.
Definition astate_frameR {Sl Sr Sr' A} := @astate_frameR_ Sl Sr Sr' A.
Definition astate_A {S S' S''} := @astate_A_ S S' S''.
Definition astate_A' {S S' S''} := @astate_A'_ S S' S''.
Definition astate_C {S S'} := @astate_C_ S S'.
Definition astate_GET {I T} := @astate_GET_ I T.
Definition astate_SET {I T} := @astate_SET_ I T.

Definition runt_AState (S S' A : Type) : Type := S -> A * S'.

Definition run_AState_raw :
  forall S S' A, AState S S' A -> runt_AState S S' A :=
  @AState_rect (fun S S' A _ => S -> A * S')
  (* return *) (fun _ _ a s => (a, s))
  (* bind *)   (fun _ _ _ _ _ _ f _ g s => let (a, s') := f s in g a s')
  (* frameL *) (fun _ _ _ _ _ f '(sl, sr) =>
                  let (a, sl') := f sl in (a, (sl', sr)))
  (* frameR *) (fun _ _ _ _ _ f '(sl, sr) =>
                  let (a, sr') := f sr in (a, (sl, sr')))
  (* A *)      (fun _ _ _ '(s, s', s'') => (tt, (s, (s', s''))))
  (* A' *)     (fun _ _ _ '(s, (s', s'')) => (tt, (s, s', s'')))
  (* C *)      (fun _ _ '(s, s') => (tt, (s', s)))
  (* get *)    (fun _ _ i a => (a (fin_decode i), a))
  (* set *)    (fun _ _ i x a => (tt, ffun_set (fin_decode i) x a)).

Definition run_AState
           (S : copyType) (S' A : Type) (m : AState S S' A) (s : S) : A * S' :=
  run_AState_raw m (copy s).

Lemma run_AStateE_ret (S : copyType) (A : Type) (a : A) (s : S) :
  run_AState (astate_ret a) s = (a, s).
Proof. by rewrite /run_AState copyE. Qed.

Lemma run_AStateE_bind
      (S S' : copyType) (S'' A B : Type)
      (f : AState S S' A) (g : A -> AState S' S'' B) (s : S) :
  run_AState (astate_bind f g) s =
  let (a, s') := run_AState f s in run_AState (g a) s'.
Proof.
by rewrite /run_AState /=;
  case: (run_AState_raw _ _) => a s'; rewrite copyE.
Qed.

Lemma run_AStateE_frameL
      (Sl Sr : copyType) (Sl' : Type) (A : Type)
      (f : AState Sl Sl' A) (s : Sl * Sr) :
  run_AState (astate_frameL f) s =
  let (sl, sr) := s in let (a, sl') := run_AState f sl in (a, (sl', sr)).
Proof. by case: s => sl sr; rewrite /run_AState !copyE. Qed.

Lemma run_AStateE_frameR
      (Sl Sr : copyType) (Sr' : Type) (A : Type)
      (f : AState Sr Sr' A) (s : Sl * Sr) :
  run_AState (astate_frameR f) s =
  let (sl, sr) := s in let (a, sr') := run_AState f sr in (a, (sl, sr')).
Proof. by case: s => sl sr; rewrite /run_AState !copyE. Qed.

Lemma run_AStateE_A (S S' S'' : copyType) (s : S * S' * S'') :
  run_AState astate_A s = let: (s, s', s'') := s in (tt, (s, (s', s''))).
Proof. by move: s => [[s s'] s'']; rewrite /run_AState copyE. Qed.

Lemma run_AStateE_A' (S S' S'' : copyType) (s : S * (S' * S'')) :
  run_AState astate_A' s = let: (s, (s', s'')) := s in (tt, (s, s', s'')).
Proof. by move: s => [s [s' s'']]; rewrite /run_AState copyE. Qed.

Lemma run_AStateE_C (S S' : copyType) (s : S * S') :
  run_AState astate_C s = let (s, s') := s in (tt, (s', s)).
Proof. by case: s => s s'; rewrite /run_AState copyE. Qed.

Lemma run_AStateE_GET
      (I : finType) (T : Type) (s : {ffun I -> T}) (i : 'I_#|I|) :
  run_AState (astate_GET i) s = (s (fin_decode i), s).
Proof. by rewrite /run_AState copyE. Qed.

Lemma run_AStateE_SET
      (I : finType) (T : Type) (s : {ffun I -> T}) (i : 'I_#|I|) (x : T) :
  run_AState (astate_SET i x) s = (tt, ffun_set (fin_decode i) x s).
Proof. by rewrite /run_AState copyE. Qed.

Notation astate_get i := (astate_GET (fin_encode i)).
Notation astate_set i x := (astate_SET (fin_encode i) x).

Definition run_AStateE :=
  (((fin_encodeK, run_AStateE_ret, run_AStateE_bind),
    (run_AStateE_frameL, run_AStateE_frameR)),
   ((run_AStateE_A, run_AStateE_A', run_AStateE_C),
    (run_AStateE_GET, run_AStateE_SET))).

Notation "x <- y ; f" :=
  (astate_bind y (fun x => f)) (at level 65, right associativity).
Notation "y ;; f" :=
  (astate_bind y (fun _ => f)) (at level 65, right associativity).

Notation AState' T A := (AState T T A).

Global Opaque run_AState run_AState_raw.

(* Arrangement *)

Definition astate_AC (S S' S'' : Type) :
  AState (S * (S' * S'')) (S' * (S * S'')) unit :=
  astate_A';; astate_frameL astate_C;; astate_A.

Definition astate_CA (S S' S'' : Type) :
  AState ((S * S') * S'') ((S * S'') * S') unit :=
  astate_A;; astate_frameR astate_C;; astate_A'.

(* Iteration *)

Section Iteration_ordinal.

Variable (n : nat) (S : copyType) (A : Type)
         (f : 'I_n -> A -> A) (g : 'I_n -> A -> AState' S A).

Fixpoint iterate_revord (i : nat) (x : A) : i <= n -> A :=
  match i with
    | 0 => fun _ => x
    | i'.+1 => fun (H : i' < n) =>
                 iterate_revord (i := i') (f (Ordinal H) x) (ltnW H)
  end.

Lemma iterate_revord_eq (x : A) :
  iterate_revord x (leqnn n) = foldr f x (enum 'I_n).
Proof.
move: (f_equal rev (val_enum_ord n)); rewrite -map_rev -{2}(revK (enum _)).
move: (rev _) (leqnn _) => /= xs;
  move: {1 5 6}n => i Hi; elim: i Hi x xs => [| i IH] H x; first by case.
rewrite -{1}addn1 iota_add add0n /= rev_cat //=; case => //= i' xs [] H0 H1.
have <-: i' = Ordinal H by apply val_inj.
by rewrite rev_cons -cats1 foldr_cat /= -(IH (ltnW H)).
Qed.

Fixpoint miterate_revord (i : nat) (x : A) : i <= n -> AState' S A :=
  match i with
    | 0 => fun _ => astate_ret x
    | i'.+1 =>
      fun (H : i' < n) =>
        astate_bind (g (Ordinal H) x) (fun y => miterate_revord y (ltnW H))
  end.

Lemma run_miterate_revord (x : A) (s : S) :
  run_AState (miterate_revord x (leqnn n)) s =
  foldr (fun i '(x, s) => run_AState (g i x) s) (x, s) (enum 'I_n).
Proof.
move: (f_equal rev (val_enum_ord n)); rewrite -map_rev -{2}(revK (enum _)).
move: (rev _) (leqnn _) => /= xs;
  move: {1 5 6}n => i Hi; elim: i Hi x xs s => [| i IH] H x;
  first by case => //= s _; rewrite run_AStateE.
rewrite -{1}addn1 iota_add add0n /= rev_cat //=; case => //= i' xs s [] H0 H1.
have <-: i' = Ordinal H by apply val_inj.
by rewrite run_AStateE rev_cons -cats1 foldr_cat /=;
  case: (run_AState (g i' x) s) => s' y; rewrite -(IH (ltnW H)).
Qed.

End Iteration_ordinal.

Section Iteration_finType.

Lemma rev_enum_ord n : rev (enum 'I_n) = [seq rev_ord i | i <- enum 'I_n].
Proof.
apply/(inj_map val_inj).
move: (map_comp (fun x => n - x.+1) val (enum 'I_n)) (val_enum_ord n).
rewrite -(map_comp val (@rev_ord _)) !/comp /= map_rev => -> ->.
rewrite -{2}(subnn n); elim: {1 3 6 7}n (leqnn n) => // i IH H.
by rewrite -{1}(addn1 i) iota_add add0n /=
           rev_cat /= subnSK // -IH ?subKn // ltnW.
Qed.

Variable (T : finType) (S : copyType) (A : Type)
         (f : T -> A -> A) (g : T -> A -> AState' S A).

Definition iterate_fin (x : A) : A :=
  iterate_revord (fun i x => f (raw_fin_decode (rev_ord i)) x) x (leqnn $|T|).

Lemma iterate_fin_eq x : iterate_fin x = foldl (fun x => f ^~ x) x (enum T).
Proof.
by rewrite /iterate_fin iterate_revord_eq -(revK (enum T)) enumT unlock
           ord_enumE foldl_rev -map_rev rev_enum_ord -map_comp foldr_map.
Qed.

Definition iterate_revfin (x : A) : A :=
  iterate_revord (fun i x => f (raw_fin_decode i) x) x (leqnn $|T|).

Lemma iterate_revfin_eq x : iterate_revfin x = foldr f x (enum T).
Proof.
by rewrite /iterate_revfin iterate_revord_eq
           enumT unlock ord_enumE [X in _ = X]foldr_map.
Qed.

Definition miterate_fin (x : A) : AState' S A :=
  miterate_revord (fun i => g (raw_fin_decode (rev_ord i))) x (leqnn $|T|).

Lemma run_miterate_fin (x : A) (s : S) :
  run_AState (miterate_fin x) s =
  foldl (fun '(x, s) i => run_AState (g i x) s) (x, s) (enum T).
Proof.
rewrite /miterate_fin run_miterate_revord -(revK (enum T)) enumT unlock
        ord_enumE foldl_rev -map_rev rev_enum_ord -map_comp foldr_map.
by elim: (enum _) => //= i xs ->; case: (foldr _ _ _).
Qed.

Definition miterate_revfin (x : A) : AState' S A :=
  miterate_revord (fun i => g (raw_fin_decode i)) x (leqnn $|T|).

Lemma run_miterate_revfin (x : A) (s : S) :
  run_AState (miterate_revfin x) s =
  foldr (fun i '(x, s) => run_AState (g i x) s) (x, s) (enum T).
Proof.
by rewrite /miterate_revfin run_miterate_revord enumT unlock ord_enumE
           [X in _ = X]foldr_map /comp.
Qed.

End Iteration_finType.

Set Printing Width 79.

Definition swap (I : finType) {A : Type} (i j : I) :
  AState' {ffun I -> A} unit :=
  x <- astate_get i; y <- astate_get j; astate_set i y;; astate_set j x.

Lemma run_swap (I : finType) (A : Type) (i j : I) (f : {ffun I -> A}) :
  run_AState (swap i j) f = (tt, [ffun k => f (tperm i j k)]).
Proof.
rewrite !run_AStateE.
congr pair.
apply/ffunP => k.
rewrite !ffunE.
case: tpermP; do!case: eqP; congruence.
Restart.
by rewrite !run_AStateE; congr pair; apply/ffunP => k; rewrite !ffunE;
  case: tpermP; do!case: eqP; congruence.
Qed.

Global Opaque swap.

Definition SWAP (I : finType) {A : Type} (i j : 'I_#|I|) :
  AState' {ffun I -> A} unit :=
  x <- astate_GET i; y <- astate_GET j; astate_SET i y;; astate_SET j x.

Lemma run_SWAP (I : finType) (A : Type) (i j : 'I_#|I|) (f : {ffun I -> A}) :
  run_AState (SWAP i j) f =
  (tt, [ffun k => f (tperm (fin_decode i) (fin_decode j) k)]).
Proof.
by rewrite !run_AStateE; congr pair; apply/ffunP => k; rewrite !ffunE;
  case: tpermP; do!case: eqP; congruence.
Qed.

Global Opaque SWAP.

(* Monad laws and equational theory of the array state monad *)

Module equational_theory.

Notation "x =m y" :=
  (run_AState x =1 run_AState y) (at level 70, no associativity).

(*
Lemma left_id sig A B (a : A) (f : A -> AState sig B) :
  a' <- Monad.ret _ a; f a'  =m  f a.
Proof. done. Qed.

Lemma right_id sig A (a : AState sig A) : a' <- a; Monad.ret _ a'  =m  a.
Proof.
by case: a => //= {sig A} =>
  [sig A B a f s | I T sig A x [s a] | I T sig A x [s a]] //;
  case: (run_AState _ s) => //= s' ?; case: (run_AState _ s').
Qed.

Lemma assoc
  sig A B C (a : AState sig A) (f : A -> AState sig B) (g : B -> AState sig C) :
  a' <- a; b <- f a'; g b  =m  b <- (a' <- a; f a'); g b.
Proof. by move => s /=; case: (run_AState a s). Qed.

Lemma lift_distr I T sig A B (a : AState sig A) (f : A -> AState sig B) :
  astate_lift (a' <- a; f a') =m
  a' <- @astate_lift I T _ _ a; astate_lift (f a').
Proof. by move => /= [s s']; case: (run_AState a s). Qed.

Lemma set_return_unit I T sig (i : 'I_#|I|) (x : T) :
  astate_SET (sig := sig) i x  =m  astate_SET i x;; Monad.ret _ tt.
Proof. by case. Qed.

Lemma get_lift I T sig A B (i : 'I_#|I|)
      (a : AState sig A) (f : A -> T -> AState ((I, T) :: sig) B) :
  x <- astate_GET i; a' <- astate_lift a; f a' x =m
  a' <- astate_lift a; x <- astate_GET i; f a' x.
Proof. by move => /= [s s']; case: (run_AState a s). Qed.

Lemma set_lift I T sig A (i : 'I_#|I|) (x : T) (a : AState sig A) :
  astate_SET (sig := sig) i x;; astate_lift a =m
  a' <- astate_lift a; astate_SET i x;; Monad.ret _ a'.
Proof. by move => /= [s s']; case: (run_AState a s). Qed.

Lemma get_set_s I T sig (i : 'I_#|I|) :
  x <- @astate_GET I T sig i; astate_SET i x  =m  astate_ret tt.
Proof.
by move => /= [s s']; congr (_, _, _); apply/ffunP => j;
  rewrite ffunE; case: eqP => //= -> {j}.
Qed.

Lemma get_get_s
      I T sig A (i : 'I_#|I|) (f : T -> T -> AState ((I, T) :: sig) A) :
  x <- astate_GET i; y <- astate_GET i; f x y  =m  x <- astate_GET i; f x x.
Proof. done. Qed.

Lemma set_set_s I T sig (i : 'I_#|I|) (x y : T) :
  astate_SET (sig := sig) i x;; astate_SET i y  =m  astate_SET i y.
Proof.
by move => /= [s s']; congr (_, _, _);
   apply/ffunP => j; rewrite !ffunE; case: eqP.
Qed.

Lemma set_get_s I T sig (i : 'I_#|I|) (x : T) :
  astate_SET (sig := sig) i x;; astate_GET i =m
  astate_SET i x;; Monad.ret _ x.
Proof. by move => /= [s s'] /=; congr (_, _, _); rewrite !ffunE eqxx. Qed.

Lemma get_get_d
      I T sig A (i j : 'I_#|I|) (f : T -> T -> AState ((I, T) :: sig) A) :
  x <- astate_GET (sig := sig) i; y <- astate_GET j; f x y =m
  y <- astate_GET j; x <- astate_GET i; f x y.
Proof. done. Qed.

Lemma set_set_d I T sig (i j : 'I_#|I|) (x y : T) :
  i != j ->
  astate_SET (sig := sig) i x;; astate_SET j y =m
  astate_SET j y;; astate_SET i x.
Proof.
move => /= /eqP H [s s']; congr (_, _, _); apply/ffunP => k; rewrite !ffunE;
  do !case: eqP; try congruence; rewrite -(fin_encodeK k) =>
  /(can_inj (@fin_decodeK _)) H0 /(can_inj (@fin_decodeK _)) H1; congruence.
Qed.

Lemma set_get_d I T sig (i j : 'I_#|I|) (x : T) :
  i != j ->
  astate_SET (sig := sig) i x;; astate_GET j =m
  y <- astate_GET j; astate_SET i x;; Monad.ret _ y.
Proof.
by move => /= H [s s']; congr (_, _, _); rewrite /= !ffunE;
   rewrite (inj_eq (can_inj (@fin_decodeK _))) eq_sym (negbTE H).
Qed.
*)

End equational_theory.
