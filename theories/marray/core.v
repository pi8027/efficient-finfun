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

Module Type CopyableMixinSig.

Parameters
  (mixin_of : Type -> Type)
  (copy : forall (T : Type), mixin_of T -> T -> T)
  (copyE : forall (T : Type) (C : mixin_of T) (x : T), copy C x = x)
  (ffun_mixin : forall (I : finType) (T : Type), mixin_of {ffun I -> T})
  (prod_mixin :
     forall (T1 T2 : Type) (C1 : mixin_of T1) (C2 : mixin_of T2),
       mixin_of (T1 * T2)).

End CopyableMixinSig.

Module CopyableMixin : CopyableMixinSig.

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

End CopyableMixin.

Module Copyable.

Structure type : Type := Pack {sort; _ : CopyableMixin.mixin_of sort }.

Section ClassDef.
Variable (T : Type) (cT : type).

Definition class :=
  let: Pack _ c := cT return CopyableMixin.mixin_of (sort cT) in c.
Definition pack c := @Pack T c.
Definition clone := fun c & sort cT -> T & phant_id (pack c) cT => pack c.

End ClassDef.

Module Exports.
Coercion sort : type >-> Sortclass.
Notation copyType := type.
Notation "[ 'copyMixin' 'of' T ]" :=
  (class _ : CopyableMixin.mixin_of T)
    (at level 0, format "[ 'copyMixin' 'of' T ]") : form_scope.
Notation "[ 'copyType' 'of' T ]" :=
  (@clone T _ _ idfun id).
End Exports.

End Copyable.

Export Copyable.Exports.

Definition copy (T : copyType) : T -> T :=
  CopyableMixin.copy (Copyable.class T).

Lemma copyE (T : copyType) (x : T) : copy x = x.
Proof.
by rewrite /copy; case: T x => /= T m x; rewrite CopyableMixin.copyE.
Qed.

Canonical finfun_copyType (I : finType) (T : Type) : copyType :=
  @Copyable.Pack {ffun I -> T} (CopyableMixin.ffun_mixin I T).

Canonical prod_copyType (T1 T2 : copyType) : copyType :=
  @Copyable.Pack
    (T1 * T2)
    (CopyableMixin.prod_mixin (Copyable.class T1) (Copyable.class T2)).

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
  (* GET *)    (fun _ _ i s => (s (fin_decode i), s))
  (* SET *)    (fun _ _ i x s => (tt, ffun_set (fin_decode i) x s)).

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

Notation "'mlet' x := y 'in' f" :=
  (astate_bind y (fun x => f))
  (x ident, at level 65, right associativity).
Notation "'mlet' ' x := y 'in' f" :=
  (astate_bind y (fun x => f))
  (x pattern, at level 65, right associativity).
Notation "y ;; f" :=
  (astate_bind y (fun _ => f))
  (at level 65, right associativity).

(* Monad laws and equational theory of the array state monad *)

Module equational_theory.

Notation "x =m y" :=
  (run_AState x =1 run_AState y) (at level 70, no associativity).

Lemma left_id (S : copyType) A B (a : A) (f : A -> AState S B) :
  mlet a' := astate_ret a in f a'  =m  f a.
Proof. by move=> s; rewrite !run_AStateE. Qed.

Lemma right_id (S : copyType) A (a : AState S A) :
  mlet a' := a in astate_ret a'  =m  a.
Proof.
by move=> s; rewrite !run_AStateE;
  case: (run_AState _ _) => [x s']; rewrite !run_AStateE.
Qed.

Lemma assoc
      (S : copyType) A B C
      (a : AState S A) (f : A -> AState S B) (g : B -> AState S C) :
  mlet a' := a in mlet b := f a' in g b  =m
  mlet b := mlet a' := a in f a' in g b.
Proof.
by move=> s; rewrite !run_AStateE;
  case: (run_AState _ _) => [x s']; rewrite !run_AStateE.
Qed.

Lemma frameL_distr
      (Sl Sr : copyType) A B (a : AState Sl A) (f : A -> AState Sl B) :
  astate_frameL (Sr := Sr) (mlet a' := a in f a') =m
  mlet a' := astate_frameL a in astate_frameL (f a').
Proof.
case=> sl sr; rewrite !run_AStateE.
by case: (run_AState a sl) => x sl'; rewrite !run_AStateE.
Qed.

Lemma frameR_distr
      (Sl Sr : copyType) A B (a : AState Sr A) (f : A -> AState Sr B) :
  astate_frameR (Sl := Sl) (mlet a' := a in f a') =m
  mlet a' := astate_frameR a in astate_frameR (f a').
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
  mlet x := astate_frameL a in mlet y := astate_frameR b in f x y =m
  mlet y := astate_frameR b in mlet x := astate_frameL a in f x y.
Proof with rewrite !run_AStateE.
case=> sl sr...
case: {1 3}(run_AState a _) (erefl (run_AState a sl)) => x sl'...
by case: (run_AState b _) => y sr'; rewrite !run_AStateE => <-.
Qed.

Lemma get_set_s (I : finType) T (i : 'I_#|I|) :
  mlet x := astate_GET (T := T) i in astate_SET i x  =m  astate_ret tt.
Proof. by move=> s; rewrite !run_AStateE subst_id. Qed.

Lemma get_get_s
      (I : finType) T A (i : 'I_#|I|) (f : T -> T -> AState {ffun I -> T} A) :
  mlet x := astate_GET i in mlet y := astate_GET i in f x y  =m
  mlet x := astate_GET i in f x x.
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
  mlet x := astate_GET i in mlet y := astate_GET j in f x y =m
  mlet y := astate_GET j in mlet x := astate_GET i in f x y.
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
  mlet y := astate_GET j in astate_SET i x;; astate_ret y.
Proof.
by move=> H s; rewrite !run_AStateE; congr (_, _);
  rewrite !ffunE (can_eq (@fin_decodeK _)) eq_sym (negbTE H).
Qed.

End equational_theory.

(* Iteration *)

Lemma rev_enum_ord n : rev (enum 'I_n) = [seq rev_ord i | i <- enum 'I_n].
Proof.
apply/(inj_map val_inj).
move: (map_comp (fun x => n - x.+1) val (enum 'I_n)) (val_enum_ord n).
rewrite -(map_comp val (@rev_ord _)) !/comp /= map_rev => -> ->.
rewrite -{2}(subnn n); elim: {1 3 6 7}n (leqnn n) => // i IH H.
by rewrite -{1}(addn1 i) iota_add add0n /=
           rev_cat /= subnSK // -IH ?subKn // ltnW.
Qed.

Lemma foldl_map
      (T T' R : Type) (f : R -> T' -> R) (g : T -> T') (z : R) (s : seq T) :
  foldl f z (map g s) = foldl (fun z x => f z (g x)) z s.
Proof. by elim: s z; simpl. Qed.

Section Iteration_ordinal.

Variable (n : nat) (A : Type).

Section iterate_revord.

Variable (f : 'I_n -> A -> A).

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
rewrite -{1}addn1 iota_add add0n /= rev_cat => -[] //= i' xs [] H0 H1.
have <-: i' = Ordinal H by apply val_inj.
by rewrite rev_cons -cats1 foldr_cat /= -(IH (ltnW H)).
Qed.

End iterate_revord.

(*
Fixpoint miterate_revord (S : Type) (g : 'I_n -> A -> AState S A)
                         (i : nat) (x : A) : i <= n -> AState S A :=
  match i with
    | 0 => fun _ => astate_ret x
    | i'.+1 =>
      fun (H : i' < n) =>
        mlet y := g (Ordinal H) x in
        @miterate_revord _ g i' y (ltnW H)
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
*)

Definition miterate_revord (S : Type) (g : 'I_n -> A -> AState S A) :=
  fix rec (i : nat) (x : A) : i <= n -> AState S A :=
  match i with
    | 0 => fun _ => astate_ret x
    | i'.+1 =>
      fun (H : i' < n) =>
        astate_bind (g (Ordinal H) x) (fun y => rec i' y (ltnW H))
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

Definition miterate_ord
           (S : Type) (g : 'I_n -> A -> AState S A) (x : A) :=
  miterate_revord (fun i => g (rev_ord i)) x (leqnn n).

Lemma run_miterate_ord
      (S : copyType) (g : 'I_n -> A -> AState S A) (x : A) (s : S) :
  run_AState (miterate_ord g x) s =
  foldl (fun '(x, s) i => run_AState (g i x) s) (x, s) (enum 'I_n).
Proof.
rewrite run_miterate_revord -{2}(revK (enum _))
        foldl_rev rev_enum_ord foldr_map.
by elim: (enum _) => //= i xs ->; case: (foldr _ _ _).
Qed.

Definition miterate_revord' (S : Type) (g : 'I_n -> AState S unit) :=
  fix rec (i : nat) : i <= n -> AState S unit :=
  match i with
    | 0 => fun _ => astate_ret tt
    | i'.+1 => fun H : i' < n => g (Ordinal H);; rec i' (ltnW H)
  end.

Lemma run_miterate_revord'
      (S : copyType) (g : 'I_n -> AState S unit) (s : S) :
  run_AState (miterate_revord' g (leqnn n)) s =
  (tt, foldr (fun i s => (run_AState (g i) s).2) s (enum 'I_n)).
Proof.
move: (f_equal rev (val_enum_ord n)); rewrite -map_rev -{2}(revK (enum _)).
move: (rev _) (leqnn _) => /= xs;
  move: {1 5 6}n => i Hi; elim: i Hi xs s => [| i IH] H;
  first by case=> //= s _; rewrite run_AStateE.
rewrite -{1}addn1 iota_add add0n /= rev_cat => -[] //= i' xs s [] H0 H1.
have <-: i' = Ordinal H by apply val_inj.
by rewrite run_AStateE rev_cons -cats1 foldr_cat /=;
  case: (run_AState (g i') s) => s' y; rewrite -(IH (ltnW H)).
Qed.

End Iteration_ordinal.

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
           enumT unlock ord_enumE [RHS]foldr_map.
Qed.

Definition miterate_both
           (S : Type) (g : 'I_#|T| -> T -> A -> AState S A) (x : A) :
  AState S A :=
  miterate_ord (fun i => g (cast_ord (esym (cardT' _)) i) (raw_fin_decode i)) x.

(*
Definition miterate_both'
           (S : Type) (g : 'I_#|T| -> T -> A -> AState S A) (x : A) :
  AState S A :=
  miterate_revord
    (fun i => let i' := rev_ord i in
              g (cast_ord (esym (cardT' _)) i') (raw_fin_decode i'))
    x (leqnn $|T|).

Goal miterate_both = miterate_both'.
Proof. reflexivity. Qed.
*)

Lemma run_miterate_both
      (S : copyType) (g : 'I_#|T| -> T -> A -> AState S A) (x : A) (s : S) :
  run_AState (miterate_both g x) s =
  foldl (fun '(x, s) i => run_AState (g (fin_encode i) i x) s) (x, s) (enum T).
Proof.
rewrite run_miterate_ord enumT (unlock finEnum_unlock) ord_enumE
        [RHS]foldl_map.
elim: (enum _) {x s} (x, s) => //= o os IH [x s]; rewrite -IH.
by rewrite (unlock fin_encode_unlock) raw_fin_decodeK.
Qed.

Definition miterate_fin
           (S : Type) (g : T -> A -> AState S A) (x : A) : AState S A :=
  miterate_both (fun _ i => g i) x.

Lemma run_miterate_fin
      (S : copyType) (g : T -> A -> AState S A) (x : A) (s : S) :
  run_AState (miterate_fin g x) s =
  foldl (fun '(x, s) i => run_AState (g i x) s) (x, s) (enum T).
Proof. by rewrite run_miterate_both. Qed.

Definition miterate_revboth
           (S : Type) (g : 'I_#|T| -> T -> A -> AState S A) (x : A) :
  AState S A :=
  miterate_revord
    (fun i => g (cast_ord (esym (cardT' _)) i) (raw_fin_decode i))
    x (leqnn $|T|).

Lemma run_miterate_revboth
      (S : copyType) (g : 'I_#|T| -> T -> A -> AState S A) (x : A) (s : S) :
  run_AState (miterate_revboth g x) s =
  foldr (fun i '(x, s) => run_AState (g (fin_encode i) i x) s) (x, s) (enum T).
Proof.
rewrite run_miterate_revord enumT (unlock finEnum_unlock) ord_enumE
        [RHS]foldr_map.
by elim: (enum _) => //= o os <-;
  rewrite (unlock fin_encode_unlock) raw_fin_decodeK.
Qed.

Definition miterate_revfin
           (S : Type) (g : T -> A -> AState S A) (x : A) : AState S A :=
  miterate_revboth (fun _ i => g i) x.

Lemma run_miterate_revfin
      (S : copyType) (g : T -> A -> AState S A) (x : A) (s : S) :
  run_AState (miterate_revfin g x) s =
  foldr (fun i '(x, s) => run_AState (g i x) s) (x, s) (enum T).
Proof. by rewrite run_miterate_revboth. Qed.

Definition miterate_revfin'
           (S : copyType) (g : T -> AState S unit) : AState S unit :=
  miterate_revord' (fun i => g (raw_fin_decode i)) (leqnn $|T|).

Lemma run_miterate_revfin'
      (S : copyType) (g : T -> AState S unit) (s : S) :
  run_AState (miterate_revfin' g) s =
  (tt, foldr (fun i s => (run_AState (g i) s).2) s (enum T)).
Proof.
by rewrite run_miterate_revord' enumT unlock ord_enumE
           [X in _ = (_, X)]foldr_map.
Qed.

End Iteration_finType.

(* Swap and permutation utilities *)

Definition perm_ffun
           (I : finType) (A : Type) (p : {perm I}) (f : {ffun I -> A}) :=
  [ffun i => f (p i)].

Lemma perm_ffunE1 (I : finType) (A : Type) (f : {ffun I -> A}) :
  perm_ffun 1%g f = f.
Proof. by apply/ffunP => i; rewrite !ffunE permE. Qed.

Lemma perm_ffunEM
      (I : finType) (A : Type) (p p' : {perm I}) (f : {ffun I -> A}) :
  perm_ffun (p * p') f = perm_ffun p (perm_ffun p' f).
Proof. by apply/ffunP => i; rewrite !ffunE permM. Qed.

Definition SWAP (I : finType) {A : Type} (i j : 'I_#|I|) :
  AState {ffun I -> A} unit :=
  mlet x := astate_GET i in
  mlet y := astate_GET j in
  astate_SET i y;; astate_SET j x.

Lemma run_SWAP (I : finType) (A : Type) (i j : 'I_#|I|) (f : {ffun I -> A}) :
  run_AState (SWAP i j) f =
  (tt, perm_ffun (tperm (fin_decode i) (fin_decode j)) f).
Proof.
rewrite !run_AStateE.
congr pair.
apply/ffunP => k.
rewrite !ffunE.
rewrite permE /=; do!case: eqP; congruence.
Restart.
rewrite !run_AStateE; congr pair; apply/ffunP => k.
rewrite !ffunE permE /=; do !case: eqP; congruence.
Qed.

Definition swap (I : finType) {A : Type} (i j : I) :
  AState {ffun I -> A} unit :=
  SWAP (fin_encode i) (fin_encode j).

Lemma run_swap (I : finType) (A : Type) (i j : I) (f : {ffun I -> A}) :
  run_AState (swap i j) f = (tt, perm_ffun (tperm i j) f).
Proof. by rewrite run_SWAP !fin_encodeK. Qed.

Global Opaque SWAP swap.
