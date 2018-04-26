Require Import all_ssreflect fingroup perm.

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

Definition Sign : Type := seq (finType * Type).

Implicit Types (I J K : finType) (sig : Sign).

Inductive AState : Sign -> Type -> Type :=
  | astate_ret_ :
      forall {sig} {A : Type}, A -> AState sig A
  | astate_bind_ :
      forall {sig} {A B : Type},
        AState sig A -> (A -> AState sig B) -> AState sig B
  | astate_lift_ :
      forall {I} {T : Type} {sig} {A : Type},
        AState sig A -> AState ((I, T) :: sig) A
  | astate_GET_ :
      forall {I} {T : Type} {sig}, 'I_#|I| -> AState ((I, T) :: sig) T
  | astate_SET_ :
      forall {I} {T : Type} {sig}, 'I_#|I| -> T -> AState ((I, T) :: sig) unit.

Fixpoint states_AState sig : Type :=
  if sig is (Ix, T) :: sig' then states_AState sig' * {ffun Ix -> T} else unit.

Definition runt_AState sig (A : Type) : Type :=
  states_AState sig -> states_AState sig * A.
Definition runt_AState_ sig (A : Type) : Type := states_AState sig -> A.

Definition ffun_set
           (I : finType) (T : Type) (i : I) (x : T) (f : {ffun I -> T}) :=
  [ffun j => if j == i then x else f j].

Lemma subst_id (I : finType) (T : Type) (i : I) (x : T) (f : {ffun I -> T}) :
  x = f i -> ffun_set i x f = f.
Proof. by move ->; apply/ffunP => j; rewrite ffunE; case: eqP => // ->. Qed.

Definition run_AState : forall sig A, AState sig A -> runt_AState sig A :=
  @AState_rect (fun sig A _ => runt_AState sig A)
  (* return *) (fun _ _ a s => (s, a))
  (* bind *)   (fun _ _ _ _ f _ g s => let (s', a) := f s in g a s')
  (* lift *)   (fun _ _ _ _ _ f '(s, a) => let (s', x) := f s in (s', a, x))
  (* get *)    (fun _ _ _ i s => (s, s.2 (fin_decode i)))
  (* set *)    (fun _ _ _ i x '(s, a) => (s, ffun_set (fin_decode i) x a, tt)).

Definition astate_ret {sig A} a := @astate_ret_ sig A a.
Definition astate_bind {sig A B} := @astate_bind_ sig A B.
Definition astate_lift {I T sig A} := @astate_lift_ I T sig A.
Definition astate_GET {I T sig} := @astate_GET_ I T sig.
Definition astate_SET {I T sig} := @astate_SET_ I T sig.

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

Notation "x =m y" :=
  (run_AState x =1 run_AState y) (at level 70, no associativity).

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

End equational_theory.

(* Iteration *)

Section Iteration_ordinal.

Variable (n : nat) (sig : Sign) (A : Type)
         (f : 'I_n -> A -> A) (g : 'I_n -> A -> AState sig A).

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

Fixpoint miterate_revord (i : nat) (x : A) : i <= n -> AState sig A :=
  match i with
    | 0 => fun _ => astate_ret x
    | i'.+1 =>
      fun (H : i' < n) =>
        astate_bind (g (Ordinal H) x) (fun y => miterate_revord y (ltnW H))
  end.

Lemma run_miterate_revord (x : A) (s : states_AState sig) :
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

Variable (T : finType) (sig : Sign) (A : Type)
         (f : T -> A -> A) (g : T -> A -> AState sig A).

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

Definition miterate_fin (x : A) : AState sig A :=
  miterate_revord (fun i => g (raw_fin_decode (rev_ord i))) x (leqnn $|T|).

Lemma run_miterate_fin (x : A) (s : states_AState sig) :
  run_AState (miterate_fin x) s =
  foldl (fun '(s, x) i => run_AState (g i x) s) (s, x) (enum T).
Proof.
rewrite /miterate_fin run_miterate_revord -(revK (enum T)) enumT unlock
        ord_enumE foldl_rev -map_rev rev_enum_ord -map_comp foldr_map.
by elim: (enum _) => //= i xs ->; case: (foldr _ _ _).
Qed.

Definition miterate_revfin (x : A) : AState sig A :=
  miterate_revord (fun i => g (raw_fin_decode i)) x (leqnn $|T|).

Lemma run_miterate_revfin (x : A) (s : states_AState sig) :
  run_AState (miterate_revfin x) s =
  foldr (fun i '(s, x) => run_AState (g i x) s) (s, x) (enum T).
Proof.
by rewrite /miterate_revfin run_miterate_revord enumT unlock ord_enumE
           [X in _ = X]foldr_map /comp.
Qed.

End Iteration_finType.

Set Printing Width 79.

Definition swap (I : finType) {A : Type} {sig : Sign} (i j : I) :
  AState ((I, A) :: sig) unit :=
  x <- astate_get i; y <- astate_get j; astate_set i y;; astate_set j x.

Lemma run_swap
      (I : finType) (A : Type) (sig : Sign) (i j : I)
      (f : {ffun I -> A}) (fs : states_AState sig) :
  run_AState (swap i j) (fs, f) = (fs, [ffun k => f (tperm i j k)], tt).
Proof.
rewrite /=.
congr (_, _, _); rewrite !fin_encodeK.
apply/ffunP => k; rewrite !ffunE /=.
case: tpermP; do!case: eqP; congruence.
Restart.
congr (_, _, _); apply/ffunP => k;
  rewrite !ffunE /= !fin_encodeK; case: tpermP; do !case: eqP; congruence.
Qed.

Global Opaque swap.

Lemma run_lift_swap
      (I I' : finType) (A B : Type) (sig : Sign) (i j : I)
      (f : {ffun I -> A}) (g : {ffun I' -> B}) (fs : states_AState sig) :
  run_AState (sig := [:: (I', B), (I, A) & sig])
             (astate_lift (swap i j)) (fs, f, g) =
  (fs, [ffun k => f (tperm i j k)], g, tt).
Proof. by rewrite /= run_swap. Qed.

Definition SWAP (I : finType) {A : Type} {sig : Sign} (i j : 'I_#|I|) :
  AState ((I, A) :: sig) unit :=
  x <- astate_GET i; y <- astate_GET j; astate_SET i y;; astate_SET j x.

Lemma run_SWAP
      (I : finType) (A : Type) (sig : Sign) (i j : 'I_#|I|)
      (f : {ffun I -> A}) (fs : states_AState sig) :
  run_AState (SWAP i j) (fs, f) =
  (fs, [ffun k => f (tperm (fin_decode i) (fin_decode j) k)], tt).
Proof.
congr (_, _, _); apply/ffunP => k;
  rewrite !ffunE /=; case: tpermP; do !case: eqP => /=; congruence.
Qed.

Global Opaque SWAP.
