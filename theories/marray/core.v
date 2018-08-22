Require Import all_ssreflect fingroup perm.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(******************************************************************************)
(* General framework for mutable array programming                            *)
(******************************************************************************)

(* copyType: provides a method for deep copying of states. *)

Definition ffun_copy
           (I : finType) (T : Type) (f : {ffun I -> T}) : {ffun I -> T} := f.

Module Type CopyableRawSig.

Parameters
  (mixin_of : Type -> Type)
  (copy : forall (T : Type), mixin_of T -> T -> T)
  (copyE : forall (T : Type) (C : mixin_of T) (x : T), copy C x = x)
  (ffun_mixin : forall (I : finType) (T : Type), mixin_of {ffun I -> T})
  (prod_mixin :
     forall (T1 T2 : Type) (C1 : mixin_of T1) (C2 : mixin_of T2),
       mixin_of (T1 * T2)).

End CopyableRawSig.

Module CopyableRaw : CopyableRawSig.

Record mixin_of_ (T : Type) : Type :=
  Mixin { copy_ : T -> T; copyE_ : forall x, copy_ x = x }.
Definition mixin_of := mixin_of_.
Definition copy (T : Type) (m : mixin_of T) :=
  let: (Mixin copy' _) := m in copy'.

Lemma copyE (T : Type) (C : mixin_of T) (x : T) : copy C x = x.
Proof. by case: C => /= copy ->. Qed.

Definition ffun_mixin (I : finType) (T : Type) : mixin_of {ffun I -> T} :=
  @Mixin _ (@ffun_copy I T) (fun _ => erefl).

Lemma prod_mixin_subproof
      (T1 T2 : Type) (C1 : mixin_of T1) (C2 : mixin_of T2) (x : T1 * T2) :
  (let (x, y) := x in (copy C1 x, copy C2 y)) = x.
Proof. by case: x => x y; rewrite !copyE. Qed.

Definition prod_mixin (T1 T2 : Type) (C1 : mixin_of T1) (C2 : mixin_of T2) :
  mixin_of (T1 * T2) :=
  @Mixin (T1 * T2) (fun '(x, y) => (copy C1 x, copy C2 y))
         (prod_mixin_subproof C1 C2).

End CopyableRaw.

Module Copyable.

Structure type : Type := Pack {sort; _ : CopyableRaw.mixin_of sort }.

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

Export Copyable.Exports.

Definition copy (T : copyType) : T -> T :=
  CopyableRaw.copy (Copyable.class T).

Lemma copyE (T : copyType) (x : T) : copy x = x.
Proof. by rewrite /copy; case: T x => /= T m x; rewrite CopyableRaw.copyE. Qed.

Canonical finfun_copyType (I : finType) (T : Type) : copyType :=
  @Copyable.Pack {ffun I -> T} (CopyableRaw.ffun_mixin I T).

Canonical prod_copyType (T1 T2 : copyType) : copyType :=
  @Copyable.Pack
    (T1 * T2) (CopyableRaw.prod_mixin (Copyable.class T1) (Copyable.class T2)).

(* Array state monad *)

Definition ffun_set
           (I : finType) (T : Type) (i : I) (x : T) (f : {ffun I -> T}) :=
  [ffun j => if j == i then x else f j].

Lemma subst_id (I : finType) (T : Type) (i : I) (x : T) (f : {ffun I -> T}) :
  x = f i -> ffun_set i x f = f.
Proof. by move->; apply/ffunP => j; rewrite ffunE; case: eqP => // ->. Qed.

(*
Module Type AStateSig.

Parameters
  (AState : Type -> Type -> Type)
  (astate_ret : forall {S A : Type}, A -> AState S A)
  (astate_bind : forall {S A B : Type},
      AState S A -> (A -> AState S B) -> AState S B)
  (astate_frameL : forall {Sl Sr A : Type}, AState Sl A -> AState (Sl * Sr) A)
  (astate_frameR : forall {Sl Sr A : Type}, AState Sr A -> AState (Sl * Sr) A)
  (astate_GET : forall {I : finType} {T : Type},
      'I_#|I| -> AState {ffun I -> T} T)
  (astate_SET : forall {I : finType} {T : Type},
      'I_#|I| -> T -> AState {ffun I -> T} unit)
  (run_AState : forall (S : copyType) (A : Type), AState S A -> S -> A * S)
  (run_AStateE_ret : forall (S : copyType) (A : Type) (a : A) (s : S),
      run_AState (astate_ret a) s = (a, s))
  (run_AStateE_bind :
     forall (S : copyType) (A B : Type)
            (f : AState S A) (g : A -> AState S B) (s : S),
       run_AState (astate_bind f g) s =
       let (a, s') := run_AState f s in run_AState (g a) s')
  (run_AStateE_frameL :
     forall (Sl Sr : copyType) (A : Type) (f : AState Sl A) (s : Sl * Sr),
       run_AState (astate_frameL f) s =
       let (sl, sr) := s in let (a, sl') := run_AState f sl in (a, (sl', sr)))
  (run_AStateE_frameR :
     forall (Sl Sr : copyType) (A : Type) (f : AState Sr A) (s : Sl * Sr),
       run_AState (astate_frameR f) s =
       let (sl, sr) := s in let (a, sr') := run_AState f sr in (a, (sl, sr')))
  (run_AStateE_GET :
     forall (I : finType) (T : Type) (s : {ffun I -> T}) (i : 'I_#|I|),
       run_AState (astate_GET i) s = (s (fin_decode i), s))
  (run_AStateE_SET :
     forall (I : finType) (T : Type) (s : {ffun I -> T}) (i : 'I_#|I|) (x : T),
       run_AState (astate_SET i x) s = (tt, ffun_set (fin_decode i) x s)).

End AStateSig.
*)

Inductive AState : Type -> Type -> Type :=
  | astate_ret_ (S A : Type) : A -> AState S A
  | astate_bind_ (S A B : Type) : AState S A -> (A -> AState S B) -> AState S B
  | astate_frameL_ (Sl Sr A : Type) : AState Sl A -> AState (Sl * Sr) A
  | astate_frameR_ (Sl Sr A : Type) : AState Sr A -> AState (Sl * Sr) A
  | astate_GET_ (I : finType) (T : Type) : 'I_#|I| -> AState {ffun I -> T} T
  | astate_SET_ (I : finType) (T : Type) :
      'I_#|I| -> T -> AState {ffun I -> T} unit.

Definition astate_ret {S A} a := @astate_ret_ S A a.
Definition astate_bind {S A B} := @astate_bind_ S A B.
Definition astate_frameL {Sl Sr A} := @astate_frameL_ Sl Sr A.
Definition astate_frameR {Sl Sr A} := @astate_frameR_ Sl Sr A.
Definition astate_GET {I T} := @astate_GET_ I T.
Definition astate_SET {I T} := @astate_SET_ I T.
Notation astate_get i := (astate_GET (fin_encode i)).
Notation astate_set i x := (astate_SET (fin_encode i) x).

Definition run_AState_raw : forall S A, AState S A -> S -> A * S :=
  @AState_rect (fun S A _ => S -> A * S)
  (* return *) (fun _ _ a s => (a, s))
  (* bind *)   (fun _ _ _ _ f _ g s => let (a, s') := f s in g a s')
  (* frameL *) (fun _ _ _ _ f '(sl, sr) =>
                  let (a, sl') := f sl in (a, (sl', sr)))
  (* frameR *) (fun _ _ _ _ f '(sl, sr) =>
                  let (a, sr') := f sr in (a, (sl, sr')))
  (* get *)    (fun _ _ i a => (a (fin_decode i), a))
  (* set *)    (fun _ _ i x a => (tt, ffun_set (fin_decode i) x a)).

Definition run_AState
           (S : copyType) (A : Type) (m : AState S A) (s : S) : A * S :=
  run_AState_raw m (copy s).

Lemma run_AStateE_ret (S : copyType) (A : Type) (a : A) (s : S) :
  run_AState (astate_ret a) s = (a, s).
Proof. by rewrite /run_AState /= copyE. Qed.

Lemma run_AStateE_bind
      (S : copyType) (A B : Type)
      (f : AState S A) (g : A -> AState S B) (s : S) :
  run_AState (astate_bind f g) s =
  let (a, s') := run_AState f s in run_AState (g a) s'.
Proof.
by rewrite /run_AState /=;
  case: (run_AState_raw _ _) => a s'; rewrite copyE.
Qed.

Lemma run_AStateE_frameL
      (Sl Sr : copyType) (A : Type) (f : AState Sl A) (s : Sl * Sr) :
  run_AState (astate_frameL f) s =
  let (sl, sr) := s in let (a, sl') := run_AState f sl in (a, (sl', sr)).
Proof. by case: s => sl sr; rewrite /run_AState /= !copyE. Qed.

Lemma run_AStateE_frameR
      (Sl Sr : copyType) (A : Type) (f : AState Sr A) (s : Sl * Sr) :
  run_AState (astate_frameR f) s =
  let (sl, sr) := s in let (a, sr') := run_AState f sr in (a, (sl, sr')).
Proof. by case: s => sl sr; rewrite /run_AState /= !copyE. Qed.

Lemma run_AStateE_GET
      (I : finType) (T : Type) (s : {ffun I -> T}) (i : 'I_#|I|) :
  run_AState (astate_GET i) s = (s (fin_decode i), s).
Proof. by rewrite /run_AState /= copyE. Qed.

Lemma run_AStateE_SET
      (I : finType) (T : Type) (s : {ffun I -> T}) (i : 'I_#|I|) (x : T) :
  run_AState (astate_SET i x) s = (tt, ffun_set (fin_decode i) x s).
Proof. by rewrite /run_AState /= copyE. Qed.

Global Opaque run_AState run_AState_raw.

Definition run_AStateE :=
  ((fin_encodeK, (run_AStateE_ret, run_AStateE_bind)),
   ((run_AStateE_frameL, run_AStateE_frameR),
    (run_AStateE_GET, run_AStateE_SET))).

Notation "x <- y ; f" :=
  (astate_bind y (fun x => f))
  (at level 65, right associativity).
Notation "y ;; f" :=
  (astate_bind y (fun _ => f))
  (at level 65, right associativity).

(* Monad laws and equational theory of the array state monad *)

Module equational_theory.

Notation "x =m y" :=
  (run_AState x =1 run_AState y) (at level 70, no associativity).

Lemma left_id (S : copyType) A B (a : A) (f : A -> AState S B) :
  a' <- astate_ret a; f a'  =m  f a.
Proof. by move=> s; rewrite !run_AStateE. Qed.

Lemma right_id (S : copyType) A (a : AState S A) :
  a' <- a; astate_ret a'  =m  a.
Proof.
by move=> s; rewrite !run_AStateE;
  case: (run_AState _ _) => [x s']; rewrite !run_AStateE.
Qed.

Lemma assoc
      (S : copyType) A B C
      (a : AState S A) (f : A -> AState S B) (g : B -> AState S C) :
  a' <- a; b <- f a'; g b  =m  b <- (a' <- a; f a'); g b.
Proof.
by move=> s; rewrite !run_AStateE;
  case: (run_AState _ _) => [x s']; rewrite !run_AStateE.
Qed.

Lemma frameL_distr
      (Sl Sr : copyType) A B (a : AState Sl A) (f : A -> AState Sl B) :
  astate_frameL (Sr := Sr) (a' <- a; f a') =m
  a' <- astate_frameL a; astate_frameL (f a').
Proof.
case=> sl sr; rewrite !run_AStateE.
by case: (run_AState a sl) => x sl'; rewrite !run_AStateE.
Qed.

Lemma frameR_distr
      (Sl Sr : copyType) A B (a : AState Sr A) (f : A -> AState Sr B) :
  astate_frameR (Sl := Sl) (a' <- a; f a') =m
  a' <- astate_frameR a; astate_frameR (f a').
Proof.
case=> sl sr; rewrite !run_AStateE.
by case: (run_AState a sr) => x sr'; rewrite !run_AStateE.
Qed.

Lemma set_return_unit (I : finType) T (i : 'I_#|I|) (x : T) :
  astate_SET i x  =m  astate_SET i x;; astate_ret tt.
Proof. by move=> s; rewrite !run_AStateE. Qed.

Lemma frame_assoc
      (Sl Sr : copyType) A B C
      (a : AState Sl A) (b : AState Sr B) (f : A -> B -> AState (Sl * Sr) C) :
  x <- astate_frameL a; y <- astate_frameR b; f x y =m
  y <- astate_frameR b; x <- astate_frameL a; f x y.
Proof with rewrite !run_AStateE.
case=> sl sr...
case: {1 3}(run_AState a _) (erefl (run_AState a sl)) => x sl'...
by case: (run_AState b _) => y sr'; rewrite !run_AStateE => <-.
Qed.

Lemma get_set_s (I : finType) T (i : 'I_#|I|) :
  x <- astate_GET (T := T) i; astate_SET i x  =m  astate_ret tt.
Proof. by move=> s; rewrite !run_AStateE subst_id. Qed.

Lemma get_get_s
      (I : finType) T A (i : 'I_#|I|) (f : T -> T -> AState {ffun I -> T} A) :
  x <- astate_GET i; y <- astate_GET i; f x y  =m  x <- astate_GET i; f x x.
Proof. by move=> s; rewrite !run_AStateE. Qed.

Lemma set_set_s (I : finType) T (i : 'I_#|I|) (x y : T) :
  astate_SET i x;; astate_SET i y  =m  astate_SET i y.
Proof.
move=> s; rewrite !run_AStateE; congr (_, _).
by apply/ffunP => j; rewrite !ffunE; case: eqP.
Qed.

Lemma set_get_s (I : finType) T (i : 'I_#|I|) (x : T) :
  astate_SET i x;; astate_GET i =m astate_SET i x;; astate_ret x.
Proof. by move=> s; rewrite !run_AStateE ffunE eqxx. Qed.

Lemma get_get_d
      (I : finType) T A (i j : 'I_#|I|) (f : T -> T -> AState {ffun I -> T} A) :
  x <- astate_GET i; y <- astate_GET j; f x y =m
  y <- astate_GET j; x <- astate_GET i; f x y.
Proof. by move=> s; rewrite !run_AStateE. Qed.

Lemma set_set_d (I : finType) T (i j : 'I_#|I|) (x y : T) :
  i != j ->
  astate_SET i x;; astate_SET j y =m astate_SET j y;; astate_SET i x.
Proof.
move/eqP => H s; rewrite !run_AStateE; congr (_, _); apply/ffunP => k;
  rewrite !ffunE -!(can_eq (@fin_encodeK I)) !fin_decodeK; do !case: eqP;
  congruence.
Qed.

Lemma set_get_d (I : finType) T (i j : 'I_#|I|) (x : T) :
  i != j ->
  astate_SET i x;; astate_GET j =m
  y <- astate_GET j; astate_SET i x;; astate_ret y.
Proof.
by move=> H s; rewrite !run_AStateE; congr (_, _);
  rewrite !ffunE (can_eq (@fin_decodeK _)) eq_sym (negbTE H).
Qed.

End equational_theory.

(* Iteration *)

Section Iteration_ordinal.

Variable (n : nat) (A : Type).

Fixpoint iterate_revord
         (i : nat) (f : 'I_n -> A -> A) (x : A) : i <= n -> A :=
  match i with
    | 0 => fun _ => x
    | i'.+1 => fun (H : i' < n) =>
                 iterate_revord (i := i') f (f (Ordinal H) x) (ltnW H)
  end.

Lemma iterate_revord_eq (f : 'I_n -> A -> A) (x : A) :
  iterate_revord f x (leqnn n) = foldr f x (enum 'I_n).
Proof.
move: (f_equal rev (val_enum_ord n)); rewrite -map_rev -{2}(revK (enum _)).
move: (rev _) (leqnn _) => /= xs;
  move: {1 5 6}n => i Hi; elim: i Hi x xs => [| i IH] H x; first by case.
rewrite -{1}addn1 iota_add add0n /= rev_cat => -[] //= i' xs [] H0 H1.
have <-: i' = Ordinal H by apply val_inj.
by rewrite rev_cons -cats1 foldr_cat /= -(IH (ltnW H)).
Qed.

Fixpoint miterate_revord
         (S : Type) (i : nat) (g : 'I_n -> A -> AState S A) (x : A) :
  i <= n -> AState S A :=
  match i with
    | 0 => fun _ => astate_ret x
    | i'.+1 =>
      fun (H : i' < n) =>
        astate_bind (g (Ordinal H) x) (fun y => miterate_revord g y (ltnW H))
  end.

Lemma run_miterate_revord
      (S : copyType) (g : 'I_n -> A -> AState S A) (x : A) (s : S) :
  run_AState (miterate_revord g x (leqnn n)) s =
  foldr (fun i '(x, s) => run_AState (g i x) s) (x, s) (enum 'I_n).
Proof.
move: (f_equal rev (val_enum_ord n)); rewrite -map_rev -{2}(revK (enum _)).
move: (rev _) (leqnn _) => /= xs;
  move: {1 5 6}n => i Hi; elim: i Hi x xs s => [| i IH] H x;
  first by case=> //= s _; rewrite run_AStateE.
rewrite -{1}addn1 iota_add add0n /= rev_cat => -[] //= i' xs s [] H0 H1.
have <-: i' = Ordinal H by apply val_inj.
by rewrite run_AStateE rev_cons -cats1 foldr_cat /=;
  case: (run_AState (g i' x) s) => s' y; rewrite -(IH (ltnW H)).
Qed.

End Iteration_ordinal.

Lemma rev_enum_ord n : rev (enum 'I_n) = [seq rev_ord i | i <- enum 'I_n].
Proof.
apply/(inj_map val_inj).
move: (map_comp (fun x => n - x.+1) val (enum 'I_n)) (val_enum_ord n).
rewrite -(map_comp val (@rev_ord _)) !/comp /= map_rev => -> ->.
rewrite -{2}(subnn n); elim: {1 3 6 7}n (leqnn n) => // i IH H.
by rewrite -{1}(addn1 i) iota_add add0n /=
           rev_cat /= subnSK // -IH ?subKn // ltnW.
Qed.

Section Iteration_finType.

Variable (T : finType) (A : Type).

Definition iterate_fin (f : T -> A -> A) (x : A) : A :=
  iterate_revord (fun i x => f (raw_fin_decode (rev_ord i)) x) x (leqnn $|T|).

Lemma iterate_fin_eq (f : T -> A -> A) (x : A) :
  iterate_fin f x = foldl (fun x => f ^~ x) x (enum T).
Proof.
by rewrite /iterate_fin iterate_revord_eq -(revK (enum T)) enumT unlock
           ord_enumE foldl_rev -map_rev rev_enum_ord -map_comp foldr_map.
Qed.

Definition iterate_revfin (f : T -> A -> A) (x : A) : A :=
  iterate_revord (fun i x => f (raw_fin_decode i) x) x (leqnn $|T|).

Lemma iterate_revfin_eq (f : T -> A -> A) (x : A) :
  iterate_revfin f x = foldr f x (enum T).
Proof.
by rewrite /iterate_revfin iterate_revord_eq
           enumT unlock ord_enumE [X in _ = X]foldr_map.
Qed.

Definition miterate_fin
           (S : Type) (g : T -> A -> AState S A) (x : A) : AState S A :=
  miterate_revord (fun i => g (raw_fin_decode (rev_ord i))) x (leqnn $|T|).

Lemma run_miterate_fin
      (S : copyType) (g : T -> A -> AState S A) (x : A) (s : S) :
  run_AState (miterate_fin g x) s =
  foldl (fun '(x, s) i => run_AState (g i x) s) (x, s) (enum T).
Proof.
rewrite /miterate_fin run_miterate_revord -(revK (enum T)) enumT unlock
        ord_enumE foldl_rev -map_rev rev_enum_ord -map_comp foldr_map.
by elim: (enum _) => //= i xs ->; case: (foldr _ _ _).
Qed.

Definition miterate_revfin
           (S : copyType) (g : T -> A -> AState S A) (x : A) : AState S A :=
  miterate_revord (fun i => g (raw_fin_decode i)) x (leqnn $|T|).

Lemma run_miterate_revfin
      (S : copyType) (g : T -> A -> AState S A) (x : A) (s : S) :
  run_AState (miterate_revfin g x) s =
  foldr (fun i '(x, s) => run_AState (g i x) s) (x, s) (enum T).
Proof.
by rewrite /miterate_revfin run_miterate_revord enumT unlock ord_enumE
           [X in _ = X]foldr_map /comp.
Qed.

End Iteration_finType.

Set Printing Width 79.

(*
Definition swap (I : finType) {A : Type} (i j : I) :
  AState {ffun I -> A} unit :=
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
rewrite !run_AStateE; congr pair; apply/ffunP => k.
rewrite !ffunE; case: tpermP; do!case: eqP; congruence.
Qed.

Global Opaque swap.
*)

Definition SWAP (I : finType) {A : Type} (i j : 'I_#|I|) :
  AState {ffun I -> A} unit :=
  x <- astate_GET i; y <- astate_GET j; astate_SET i y;; astate_SET j x.

Lemma run_SWAP (I : finType) (A : Type) (i j : 'I_#|I|) (f : {ffun I -> A}) :
  run_AState (SWAP i j) f =
  (tt, [ffun k => f (tperm (fin_decode i) (fin_decode j) k)]).
Proof.
rewrite !run_AStateE; congr pair; apply/ffunP => k.
rewrite !ffunE; case: tpermP; do !case: eqP => /=; congruence.
Qed.

Definition swap (I : finType) {A : Type} (i j : I) :
  AState {ffun I -> A} unit :=
  x <- astate_get i; y <- astate_get j; astate_set i y;; astate_set j x.

Lemma run_swap (I : finType) (A : Type) (i j : I) (f : {ffun I -> A}) :
  run_AState (swap i j) f = (tt, [ffun k => f (tperm i j k)]).
Proof. by rewrite run_SWAP !fin_encodeK. Qed.

Global Opaque SWAP swap.
