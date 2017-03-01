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

Module AState_monad_laws.

Goal forall sig A B (a : A) (f : A -> AState sig B),
  Monad.run (a' <- Monad.ret _ a; f a') = Monad.run (f a).
Proof. by move => sig A B a f; rewrite /= /run_AState /=; elim: (f a). Qed.

Goal forall sig A (a : AState sig A),
  Monad.run (a' <- a; Monad.ret _ a') =1 Monad.run a.
Proof.
by move => sig A [] //= {sig A} =>
  [sig A B a f s | Ix T sig A x [s a] | Ix T sig A x [s a]] //;
  case: (run_AState _ s) => //= s' ?; case: (run_AState _ s').
Qed.

Goal forall sig A B C
            (a : AState sig A) (f : A -> AState sig B) (g : B -> AState sig C),
  Monad.run (a' <- a; b <- f a'; g b) =1 Monad.run (b <- (a' <- a; f a'); g b).
Proof. by move => sig A B C a f g s /=; case: (run_AState a s). Qed.

End AState_monad_laws.

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
