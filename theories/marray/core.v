From mathcomp Require Import all_ssreflect fingroup perm.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(******************************************************************************)
(* General framework for mutable array programming                            *)
(******************************************************************************)

Module Monad.

Structure type : Type := Pack {
  base :> Type -> Type;
  runt : Type -> Type;
  run : forall {A}, base A -> runt A;
  ret : forall {A}, A -> base A;
  bind : forall {A B}, base A -> (A -> base B) -> base B; }.

End Monad.

(*
Notation "x <- y ; f" :=
  (Monad.bind y (fun x => f)) (at level 65, right associativity).
Notation "y ;; f" :=
  (Monad.bind y (fun _ => f)) (at level 65, right associativity).
*)

Notation monadType := Monad.type.
Notation MonadType := Monad.Pack.

Coercion Monad.base : monadType >-> Funclass.

(* Identity monad *)

Record Identity (A : Type) := identity { runIdentity : A }.

Canonical Identity_monadType :=
  @MonadType
    Identity id runIdentity identity
    (fun A B (x : Identity A) (f : A -> Identity B) => f (runIdentity x)).

(* Array state monad *)

Definition ffun_set (Ix : finType) (T : Type) i x (f : {ffun Ix -> T}) :=
  [ffun j => if j == i then x else f j].

Lemma subst_id (Ix : finType) (T : Type) (f : {ffun Ix -> T}) i x :
  x = f i -> ffun_set i x f = f.
Proof. by move ->; apply/ffunP => j; rewrite ffunE; case: eqP => // ->. Qed.

Inductive AState : seq (finType * Type) -> Type -> Type :=
  | astate_ret_ : forall {sig A}, A -> AState sig A
  | astate_bind_ :
      forall {sig A B}, AState sig A -> (A -> AState sig B) -> AState sig B
  | astate_lift_ :
      forall {Ix T sig A}, AState sig A -> AState ((Ix, T) :: sig) A
  | astate_GET_ :
      forall {Ix : finType} {T sig}, 'I_#|Ix| -> AState ((Ix, T) :: sig) T
  | astate_SET_ :
      forall {Ix : finType} {T sig},
        'I_#|Ix| -> T -> AState ((Ix, T) :: sig) unit.

Fixpoint states_AState (sig : seq (finType * Type)) : Type :=
  if sig is (Ix, T) :: sig' then states_AState sig' * {ffun Ix -> T} else unit.

Definition runt_AState sig A := states_AState sig -> states_AState sig * A.
Definition runt_AState_ sig A := states_AState sig -> A.

Definition run_AState : forall sig A, AState sig A -> runt_AState sig A :=
  @AState_rect
    (fun sig A _ => runt_AState sig A)
    (fun _ _ a s => (s, a))
    (fun _ _ _ _ f _ g s => let (s', a) := f s in g a s')
    (fun _ _ _ _ _ f '(s, a) => let (s', x) := f s in (s', a, x))
    (fun _ _ _ i s => (s, s.2 (fin_decode i)))
    (fun _ _ _ i x '(s, a) => (s, ffun_set (fin_decode i) x a, tt)).

Definition astate_ret {sig A} a := @astate_ret_ sig A a.
Definition astate_bind {sig A B} := @astate_bind_ sig A B.
Definition astate_lift {Ix T sig A} := @astate_lift_ Ix T sig A.
Definition astate_GET {Ix T sig} := @astate_GET_ Ix T sig.
Definition astate_SET {Ix T sig} := @astate_SET_ Ix T sig.

Notation astate_get i := (astate_GET (fin_encode i)).
Notation astate_set i x := (astate_SET (fin_encode i) x).

Canonical AState_monadType sig :=
  @MonadType (AState sig) (runt_AState sig)
             (@run_AState sig) (@astate_ret sig) (@astate_bind sig).

Notation "x <- y ; f" :=
  (astate_bind y (fun x => f)) (at level 65, right associativity).
Notation "y ;; f" :=
  (astate_bind y (fun _ => f)) (at level 65, right associativity).

(* Monad laws and equational theory of the array state monad *)

Module equational_theory.

Implicit Types (T A B C : Type) (Ix : finType) (sig : seq (finType * Type)).

Notation "x =m y" :=
  (@Monad.run (AState_monadType _) _ x =1 @Monad.run (AState_monadType _) _ y)
  (at level 70, no associativity).

Lemma left_id sig A B (a : A) (f : A -> AState sig B) :
  a' <- Monad.ret _ a; f a'  =m  f a.
Proof. done. Qed.

Lemma right_id sig A (a : AState sig A) : a' <- a; Monad.ret _ a'  =m  a.
Proof.
by case: a => //= {sig A} =>
  [sig A B a f s | Ix T sig A x [s a] | Ix T sig A x [s a]] //;
  case: (run_AState _ s) => //= s' ?; case: (run_AState _ s').
Qed.

Lemma assoc
  sig A B C (a : AState sig A) (f : A -> AState sig B) (g : B -> AState sig C) :
  a' <- a; b <- f a'; g b  =m  b <- (a' <- a; f a'); g b.
Proof. by move => s /=; case: (run_AState a s). Qed.

Lemma lift_distr Ix T sig A B (a : AState sig A) (f : A -> AState sig B) :
  astate_lift (a' <- a; f a') =m
  a' <- @astate_lift Ix T _ _ a; astate_lift (f a').
Proof. by move => /= [s s']; case: (run_AState a s). Qed.

Lemma set_return_unit Ix T sig (i : 'I_#|Ix|) (x : T) :
  astate_SET (sig := sig) i x  =m  astate_SET i x;; Monad.ret _ tt.
Proof. by case. Qed.

Lemma get_lift Ix T sig A B (i : 'I_#|Ix|)
      (a : AState sig A) (f : A -> T -> AState ((Ix, T) :: sig) B) :
  x <- astate_GET i; a' <- astate_lift a; f a' x =m
  a' <- astate_lift a; x <- astate_GET i; f a' x.
Proof. by move => /= [s s']; case: (run_AState a s). Qed.

Lemma set_lift Ix T sig A (i : 'I_#|Ix|) (x : T) (a : AState sig A) :
  astate_SET (sig := sig) i x;; astate_lift a =m
  a' <- astate_lift a; astate_SET i x;; Monad.ret _ a'.
Proof. by move => /= [s s']; case: (run_AState a s). Qed.

Lemma get_set_s Ix T sig (i : 'I_#|Ix|) :
  x <- @astate_GET Ix T sig i; astate_SET i x  =m  astate_ret tt.
Proof.
by move => /= [s s']; congr (_, _, _); apply/ffunP => j;
  rewrite ffunE; case: eqP => //= -> {j}.
Qed.

Lemma get_get_s
      Ix T sig A (i : 'I_#|Ix|) (f : T -> T -> AState ((Ix, T) :: sig) A) :
  x <- astate_GET i; y <- astate_GET i; f x y  =m  x <- astate_GET i; f x x.
Proof. done. Qed.

Lemma set_set_s Ix T sig (i : 'I_#|Ix|) (x y : T) :
  astate_SET (sig := sig) i x;; astate_SET i y  =m  astate_SET i y.
Proof.
by move => /= [s s']; congr (_, _, _);
   apply/ffunP => j; rewrite !ffunE; case: eqP.
Qed.

Lemma set_get_s Ix T sig (i : 'I_#|Ix|) (x : T) :
  astate_SET (sig := sig) i x;; astate_GET i =m
  astate_SET i x;; Monad.ret _ x.
Proof. by move => /= [s s'] /=; congr (_, _, _); rewrite !ffunE eqxx. Qed.

Lemma get_get_d
      Ix T sig A (i j : 'I_#|Ix|) (f : T -> T -> AState ((Ix, T) :: sig) A) :
  x <- astate_GET (sig := sig) i; y <- astate_GET j; f x y =m
  y <- astate_GET j; x <- astate_GET i; f x y.
Proof. done. Qed.

Lemma set_set_d Ix T sig (i j : 'I_#|Ix|) (x y : T) :
  i != j ->
  astate_SET (sig := sig) i x;; astate_SET j y =m
  astate_SET j y;; astate_SET i x.
Proof.
move => /= /eqP H [s s']; congr (_, _, _); apply/ffunP => k; rewrite !ffunE;
  do !case: eqP; try congruence; rewrite -(fin_encodeK k) =>
  /(can_inj (@fin_decodeK _)) H0 /(can_inj (@fin_decodeK _)) H1; congruence.
Qed.

Lemma set_get_d Ix T sig (i j : 'I_#|Ix|) (x : T) :
  i != j ->
  astate_SET (sig := sig) i x;; astate_GET j =m
  y <- astate_GET j; astate_SET i x;; Monad.ret _ y.
Proof.
by move => /= H [s s']; congr (_, _, _); rewrite /= !ffunE;
   rewrite (inj_eq (can_inj (@fin_decodeK _))) eq_sym (negbTE H).
Qed.

End equational_theory.

(* Iteration *)

Section Iteration_ordinal.

Variable (n : nat) (sig : seq (finType * Type)) (A : Type)
         (f : 'I_n -> A -> A) (g : 'I_n -> A -> AState sig A).

Fixpoint iterate_revord i x : i <= n -> A :=
  match i with
    | 0 => fun _ => x
    | i'.+1 => fun (H : i' < n) =>
                 iterate_revord (i := i') (f (Ordinal H) x) (ltnW H)
  end.

Lemma iterate_revord_eq x :
  iterate_revord x (leqnn n) = foldr f x (enum 'I_n).
Proof.
move: (f_equal rev (val_enum_ord n)); rewrite -map_rev -{2}(revK (enum _)).
move: (rev _) (leqnn _) => /= xs;
  move: {1 5 6}n => i Hi; elim: i Hi x xs => [| i IH] H x; first by case.
rewrite -{1}addn1 iota_add add0n /= rev_cat //=; case => //= i' xs [] H0 H1.
have <-: i' = Ordinal H by apply val_inj.
by rewrite rev_cons -cats1 foldr_cat /= -(IH (ltnW H)).
Qed.

Fixpoint miterate_revord i x : i <= n -> AState sig A :=
  match i with
    | 0 => fun _ => astate_ret x
    | i'.+1 =>
      fun (H : i' < n) =>
        astate_bind (g (Ordinal H) x) (fun y => miterate_revord y (ltnW H))
  end.

Lemma run_miterate_revord x (s : states_AState sig) :
  run_AState (miterate_revord x (leqnn n)) s =
  foldr (fun i '(s, x) => run_AState (g i x) s) (s, x) (enum 'I_n).
Proof.
move: (f_equal rev (val_enum_ord n)); rewrite -map_rev -{2}(revK (enum _)).
move: (rev _) (leqnn _) => /= xs;
  move: {1 5 6}n => i Hi; elim: i Hi x xs s => [| i IH] H x; first by case.
rewrite -{1}addn1 iota_add add0n /= rev_cat //=; case => //= i' xs s [] H0 H1.
have <-: i' = Ordinal H by apply val_inj.
by rewrite rev_cons -cats1 foldr_cat /=;
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

Variable (T : finType) (sig : seq (finType * Type)) (A : Type)
         (f : T -> A -> A) (g : T -> A -> AState sig A).

Definition iterate_fin x : A :=
  iterate_revord (fun i x => f (raw_fin_decode (rev_ord i)) x) x (leqnn $|T|).

(*
Lemma iterate_fin_eq x : iterate_fin x = foldl (fun x => f ^~ x) x (enum T).
Proof.
rewrite /iterate_fin iterate_revord_eq -foldl_rev rev_enum_ord enumT' ord_enumE.
elim: (enum _) x => //= e es IH x. rewrite IH rev_ordK.
Qed.
*)

Definition iterate_revfin x : A :=
  iterate_revord (fun i x => f (raw_fin_decode i) x) x (leqnn $|T|).

(*
Lemma iterate_revfin_eq x : iterate_revfin x = foldr f x (enum T).
Proof.
rewrite /iterate_revfin iterate_revord_eq enumT' ord_enumE.
by elim: (enum _) x => //= e es IH x; rewrite IH.
Qed.
*)

Definition miterate_fin x : AState sig A :=
  miterate_revord (fun i => g (raw_fin_decode (rev_ord i))) x (leqnn $|T|).

(*
Lemma run_miterate_fin (x : A) (s : states_AState sig) :
  run_AState (miterate_fin x) s =
  foldl (fun '(s, x) i => run_AState (g i x) s) (s, x) (enum T).
Proof.
rewrite /miterate_fin run_miterate_revord
        -foldl_rev rev_enum_ord enumT' ord_enumE.
by elim: (enum _) s x => //= e es IH s x;
   rewrite rev_ordK; case: (run_AState _ _) => s' y; rewrite IH.
Qed.
*)

Definition miterate_revfin x : AState sig A :=
  miterate_revord (fun i => g (raw_fin_decode i)) x (leqnn $|T|).

(*
Lemma run_miterate_revfin (x : A) (s : states_AState sig) :
  run_AState (miterate_revfin x) s =
  foldr (fun i '(s, x) => run_AState (g i x) s) (s, x) (enum T).
Proof.
rewrite /miterate_revfin run_miterate_revord enumT' ord_enumE.
by elim: (enum _) s x => //= e es IH s x; rewrite IH.
Qed.
*)

End Iteration_finType.

Definition swap (I : finType) {A : Type} (i j : 'I_#|I|) :
  AState [:: (I, A)] unit :=
  x <- astate_GET i; y <- astate_GET j; astate_SET i y;; astate_SET j x.

Lemma run_swap (I : finType) (A : Type) (i j : 'I_#|I|) (f : {ffun I -> A}) :
  run_AState (swap i j) (tt, f) =
  (tt, [ffun k => f (tperm (fin_decode i) (fin_decode j) k)], tt).
Proof.
congr (tt, _, tt); apply/ffunP => k;
  rewrite !ffunE /=; case: tpermP; do !case: eqP => /=; congruence.
Qed.

Global Opaque swap.

(*
Print Finite.class_of.
  Print Choice.class_of.
    Print Equality.mixin_of.
    Print Choice.mixin_of.
  Print Finite.mixin_of.
    Print Countable.mixin_of.
*)
