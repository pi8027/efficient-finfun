From mathcomp Require Import all_ssreflect.

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

Notation "x <- y ; f" :=
  (Monad.bind y (fun x => f)) (at level 65, right associativity).
Notation "y ;; f" :=
  (Monad.bind y (fun _ => f)) (at level 65, right associativity).

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
  | astate_ret : forall {sig A}, A -> AState sig A
  | astate_bind :
      forall {sig A B}, AState sig A -> (A -> AState sig B) -> AState sig B
  | astate_lift : forall {Ix T sig A}, AState sig A -> AState ((Ix, T) :: sig) A
  | astate_GET :
      forall {Ix : finType} {T sig}, 'I_#|Ix| -> AState ((Ix, T) :: sig) T
  | astate_SET :
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

Notation astate_get i := (astate_GET (fin_encode i)).
Notation astate_set i x := (astate_SET (fin_encode i) x).

Canonical AState_monadType sig :=
  @MonadType (AState sig) (runt_AState sig)
             (@run_AState sig) (@astate_ret sig) (@astate_bind sig).

(* Monad laws and equational theory of the array state monad *)

Module equational_theory.

Implicit Types (T A B C : Type) (Ix : finType) (sig : seq (finType * Type)).

Lemma left_id sig A B (a : A) (f : A -> AState sig B) :
  Monad.run (a' <- Monad.ret _ a; f a') = Monad.run (f a).
Proof. by rewrite /= /run_AState /=; elim: (f a). Qed.

Lemma right_id sig A (a : AState sig A) :
  Monad.run (a' <- a; Monad.ret _ a') =1 Monad.run a.
Proof.
by case: a => //= {sig A} =>
  [sig A B a f s | Ix T sig A x [s a] | Ix T sig A x [s a]] //;
  case: (run_AState _ s) => //= s' ?; case: (run_AState _ s').
Qed.

Lemma assoc
  sig A B C (a : AState sig A) (f : A -> AState sig B) (g : B -> AState sig C) :
  Monad.run (a' <- a; b <- f a'; g b) =1 Monad.run (b <- (a' <- a; f a'); g b).
Proof. by move => s /=; case: (run_AState a s). Qed.

Lemma lift_distr Ix T sig A B (a : AState sig A) (f : A -> AState sig B) :
  Monad.run (a' <- @astate_lift Ix T _ _ a; astate_lift (f a')) =1
  Monad.run (astate_lift (a' <- a; f a')).
Proof. by move => /= [s s']; case: (run_AState a s). Qed.

Lemma set_return_unit Ix T sig (i : 'I_#|Ix|) (x : T) :
  Monad.run (astate_SET (sig := sig) i x) =1
  Monad.run (astate_SET i x;; Monad.ret _ tt).
Proof. by move => /= [s s']. Qed.

Lemma get_lift Ix T sig A B (i : 'I_#|Ix|)
      (a : AState sig A) (f : A -> T -> AState ((Ix, T) :: sig) B) :
  Monad.run (x <- astate_GET i; a' <- astate_lift a; f a' x) =1
  Monad.run (a' <- astate_lift a; x <- astate_GET i; f a' x).
Proof. by move => /= [s s']; case: (run_AState a s). Qed.

Lemma set_lift Ix T sig A (i : 'I_#|Ix|) (x : T) (a : AState sig A) :
  Monad.run (astate_SET (sig := sig) i x;; astate_lift a) =1
  Monad.run (a' <- astate_lift a; astate_SET i x;; Monad.ret _ a').
Proof. by move => /= [s s']; case: (run_AState a s). Qed.

Lemma get_set_s Ix T sig (i : 'I_#|Ix|) :
  Monad.run (x <- @astate_GET Ix T sig i; astate_SET i x) =1
  Monad.run (astate_ret tt).
Proof.
by move => /= [s s']; congr (_, _, _); apply/ffunP => j;
  rewrite ffunE; case: eqP => //= -> {j}.
Qed.

Lemma get_get_s
      Ix T sig A (i : 'I_#|Ix|) (f : T -> T -> AState ((Ix, T) :: sig) A) :
  Monad.run (x <- astate_GET i; y <- astate_GET i; f x y) =
  Monad.run (x <- astate_GET i; f x x).
Proof. done. Qed.

Lemma set_set_s Ix T sig (i : 'I_#|Ix|) (x : T) :
  Monad.run (astate_SET (sig := sig) i x;; astate_SET i x) =1
  Monad.run (astate_SET i x).
Proof.
by move => /= [s s']; congr (_, _, _);
   apply/ffunP => j; rewrite !ffunE; case: eqP.
Qed.

Lemma set_get_s Ix T sig (i : 'I_#|Ix|) (x : T) :
  Monad.run (astate_SET (sig := sig) i x;; astate_GET i) =1
  Monad.run (astate_SET i x;; Monad.ret _ x).
Proof. by move => /= [s s'] /=; congr (_, _, _); rewrite !ffunE eqxx. Qed.

Lemma get_get_d
      Ix T sig A (i j : 'I_#|Ix|) (f : T -> T -> AState ((Ix, T) :: sig) A) :
  Monad.run (x <- astate_GET (sig := sig) i; y <- astate_GET j; f x y) =
  Monad.run (y <- astate_GET j; x <- astate_GET i; f x y).
Proof. done. Qed.

Lemma set_set_d Ix T sig (i j : 'I_#|Ix|) (x y : T) :
  i != j ->
  Monad.run (astate_SET (sig := sig) i x;; astate_SET j y) =1
  Monad.run (astate_SET j y;; astate_SET i x).
Proof.
move => /= /eqP H [s s']; congr (_, _, _); apply/ffunP => k; rewrite !ffunE;
  do !case: eqP; try congruence; rewrite -(fin_encodeK k) =>
  /(can_inj (@fin_decodeK _)) H0 /(can_inj (@fin_decodeK _)) H1; congruence.
Qed.

Lemma set_get_d Ix T sig (i j : 'I_#|Ix|) (x : T) :
  i != j ->
  Monad.run (astate_SET (sig := sig) i x;; astate_GET j) =1
  Monad.run (y <- astate_GET j; astate_SET i x;; Monad.ret _ y).
Proof.
by move => /= H [s s']; congr (_, _, _); rewrite /= !ffunE;
   rewrite (inj_eq (can_inj (@fin_decodeK _))) eq_sym (negbTE H).
Qed.

End equational_theory.

(* Examples *)

Module Examples.

Definition swap (Ix : finType) {A : Type} i j : AState [:: (Ix, A)] unit :=
  Eval simpl in
  x <- astate_get i;
  y <- astate_get j;
  astate_set i y;; astate_set j x.

Lemma run_swap (Ix : finType) (A : Type) (i j : Ix) (f : {ffun Ix -> A}) :
  run_AState (swap i j) (tt, f) =
  (tt, [ffun k => if k == i then f j else if k == j then f i else f k], tt).
Proof.
rewrite /= !fin_encodeK.
congr (tt, _, tt); apply/ffunP => k; rewrite !ffunE; do !case: eqP; congruence.
Qed.

Opaque swap.
Lemma run_lift_swap (Ix Ix' : finType) (A B : Type) i j f g :
  run_AState (sig := [:: (Ix, A); (Ix', B)])
             (astate_lift (swap i j)) (tt, f, g) =
  (tt, [ffun k => if k == i then f j else if k == j then f i else f k], g, tt).
Proof. by rewrite /= run_swap. Qed.
Transparent swap.

End Examples.

(* Iteration *)

Section Iteration_ordinal.

Variable (n : nat) (sig : seq (finType * Type)) (A : Type)
         (f : 'I_n -> A -> AState sig A).

Lemma iterate_ord_subproof i : i < n -> n - i.+1 < n.
Proof. by move => H; rewrite subnSK // leq_subr. Qed.

Fixpoint iterate_ord (i : nat) (x : A) : i <= n -> AState sig A :=
  match i with
    | 0 => fun _ => astate_ret x
    | i'.+1 => fun (H : i' < n) =>
                 y <- f (@Ordinal n (n - i'.+1) (iterate_ord_subproof H)) x;
                 iterate_ord (i := i') y (ltnW H)
  end.

Lemma run_iterate_ord (x : A) (s : states_AState sig) :
  run_AState (iterate_ord x (leqnn n)) s =
  foldl (fun '(s, x) i => run_AState (f i x) s) (s, x) (enum 'I_n).
Proof.
move: (enum _) (leqnn _) (val_enum_ord n) => /= xs; rewrite -(subnn n).
move: {1 6 7 8}n => i Hi;
  elim: i Hi x xs s => [| i IH] H x [] //= i' xs s [] H0 H1.
have <-: i' = Ordinal (iterate_ord_subproof H) by apply val_inj.
by case: (run_AState (f i' x) s) => s' y; rewrite -(IH (ltnW H)) // H1 subnSK.
Qed.

End Iteration_ordinal.

Section Iteration_finType.

Variable (T : finType) (sig : seq (finType * Type)) (A : Type)
         (f : T -> A -> AState sig A).

Definition iterate (x : A) : AState sig A :=
  iterate_ord (fun i => f (fin_decode i)) x (leqnn #|T|).

Lemma run_iterate (x : A) (s : states_AState sig) :
  run_AState (iterate x) s =
  foldl (fun '(s, x) i => run_AState (f i x) s) (s, x) (enum T).
Proof.
rewrite /iterate run_iterate_ord enumT' ord_enumE.
by elim: (enum _) s x => //= i ixs IH s x;
   case: (run_AState _ _) => s' y; rewrite IH.
Qed.

End Iteration_finType.
