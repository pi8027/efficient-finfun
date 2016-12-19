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

Definition ffun_subst (I : finType) (T : Type) (f : {ffun I -> T}) i x :=
  [ffun j => if j == i then x else f j].

Lemma subst_id (I : finType) (T : Type) (f : {ffun I -> T}) i x :
  x = f i -> ffun_subst f i x = f.
Proof. by move ->; apply/ffunP => j; rewrite ffunE; case: eqP => // ->. Qed.

Inductive AState : seq (finType * Type) -> Type -> Type :=
  | astate_ret : forall {sig A}, A -> AState sig A
  | astate_bind :
      forall {sig A B}, AState sig A -> (A -> AState sig B) -> AState sig B
  | astate_lift :
      forall {Idx T sig A}, AState sig A -> AState ((Idx, T) :: sig) A
  | astate_get : forall {I : finType} {T sig}, I -> AState ((I, T) :: sig) T
  | astate_put :
      forall {I : finType} {T sig}, I -> T -> AState ((I, T) :: sig) unit.

Fixpoint runt_AState (sig : seq (finType * Type)) (A : Type) : Type :=
  if sig is (Idx, T) :: sig'
  then {ffun Idx -> T} -> runt_AState sig' (A * {ffun Idx -> T})
  else A.

Fixpoint run_AState_ret sig A (x : A) : runt_AState sig A :=
  match sig return runt_AState sig A with
    | [::] => x
    | (Idx, T) :: sig' => fun a => run_AState_ret sig' (x, a)
  end.

Fixpoint run_AState_bind sig A B :
         runt_AState sig A -> (A -> runt_AState sig B) -> runt_AState sig B :=
  match sig return
        runt_AState sig A -> (A -> runt_AState sig B) -> runt_AState sig B with
    | [::] => fun x f => f x
    | (Idx, T) :: sig' =>
      fun x f a => run_AState_bind (x a) (fun v => f v.1 v.2)
  end.

(*
Definition run_AState_lift Idx T sig A (x : runt_AState sig A) :
  runt_AState ((Idx, T) :: sig) A :=
  fun a => run_AState_bind x (fun x' => run_AState_ret sig (x', a)).
*)

Definition run_AState : forall sig A, AState sig A -> runt_AState sig A :=
  @AState_rect
    (fun sig A _ => runt_AState sig A)
    (fun sig _ x => run_AState_ret sig x)
    (fun sig _ _ _ x _ f => run_AState_bind x f)
    (fun I T sig A _ x a =>
       run_AState_bind x (fun x' => run_AState_ret sig (x', a)))
    (fun I T sig i a => run_AState_ret sig (a i, a))
    (fun I T sig i x a => run_AState_ret sig (tt, ffun_subst a i x)).

Canonical AState_monadType sig :=
  @MonadType (AState sig) (runt_AState sig)
             (@run_AState sig) (@astate_ret sig) (@astate_bind sig).

(******************************************************************************)
(* Union-find                                                                 *)
(******************************************************************************)

Module union_find.
Section union_find.

Variable (T : finType).
Definition G := {ffun T -> T}.
Definition Gw := {ffun T -> nat}.

Section static.

Variable (g : G).

Definition path := path (fun x y : T => (g x == y) && (x != y)).
Definition connect := fconnect g.

Lemma path_ind (P : T -> seq T -> Prop)
  (H1 : forall x, P x [::])
  (H2 : forall x xs, x != g x -> path (g x) xs -> P (g x) xs -> P x (g x :: xs))
  x xs : path x xs -> P x xs.
Proof. by elim: xs x => //= x' xs IH x /andP [/andP [/eqP <- H] H0]; auto. Qed.

Lemma connectP (x y : T) :
  reflect (exists2 p : seq T, path x p & y = last x p) (connect x y).
Proof.
apply: (iffP idP);
  last by case => xs Hxs ->; apply/connectP; exists xs => //;
          elim/path_ind: x xs / Hxs => //= x xs _ Hxs IH; rewrite eqxx IH.
rewrite /connect fconnect_orbit => H; apply/connectP.
move: (orbit_uniq g x) H; rewrite /orbit.
move: (order _ _) => n; elim: n x => //= n IH x /andP [H H0].
rewrite inE => /orP [/eqP -> // | H1]; case: n IH H H0 H1 => // n IH H H0 H1.
apply connect_trans with (g x); last by apply IH.
by apply connect1; rewrite eqxx; move: H => /=; rewrite inE negb_or => /andP [].
Qed.

Notation find := (iter #|T| g).
Definition findeq x y := find x == find y.

Definition wacycle x := iter #|T| g x == iter #|T|.+1 g x.
Definition acycle := forall x, wacycle x.

(* balanced union-find trees by rank and weight *)

(*
Variable (r w : {ffun T -> nat}).

Definition wconsistent_rank x := r x < r (g x).
Definition consistent_rank := forall x, wconsistent_rank x.

Definition wbalanced_rank x := 2 ^ r x <= #|findeq x|.
Definition balanced_rank := forall x, wbalanced_rank x.

Definition weight x := #|[pred y | connect y x]|.
Definition wconsistent_weight x := w x = weight x.
Definition consistent_weight := w = [ffun x => weight x].
*)

Lemma connect1 x : connect x (g x). Proof. by apply fconnect1. Qed.

Lemma connect_iter n x : connect x (iter n g x).
Proof. by apply fconnect_iter. Qed.

Lemma connect_find x : connect x (find x).
Proof. by rewrite connect_iter. Qed.

Section wacycle.

Variables (x : T) (Hx : wacycle x).

Lemma find_step : g (find x) = find x.
Proof. by rewrite {2}(eqP Hx). Qed.

Lemma step_find : find (g x) = find x.
Proof. by rewrite -iterSr (eqP Hx). Qed.

Lemma find_iter n : iter n g (find x) = find x.
Proof. by elim: n => // n IH; rewrite iterSr find_step IH. Qed.

Lemma iter_find n : find (iter n g x) = find x.
Proof. by rewrite -iter_add addnC iter_add find_iter. Qed.

Lemma findI : find (find x) = find x.
Proof. by rewrite find_iter. Qed.

Lemma iter_invariance n : 0 < n -> (x == iter n g x) = (x == g x).
Proof.
case: n => // n _; apply/eqP/eqP => H; last by elim: n => //= n <-.
have H0 m : iter (#|T| + m) g x = iter #|T| g x
  by rewrite addnC; elim: m => // m; rewrite addSn iterS {2}(eqP Hx) => ->.
suff ->: x = iter (#|T| * n.+1) g x by rewrite -iterS mulnS -addnS !H0.
by elim: #|T| => // c IH; rewrite mulSn iter_add -IH -H.
Qed.

Lemma find_invariance : (x == find x) = (x == g x).
Proof. by rewrite iter_invariance //; apply/card_gt0P; exists x. Qed.

Lemma path_notin xs : path x xs -> x \notin xs.
Proof.
move => Hxs; have ->: xs = [seq iter i g x | i <- iota 1 (size xs)] by
  elim/path_ind: x xs / Hxs => //= x' xs H Hxs {1}->; congr cons;
  rewrite (iota_addl 1 1) -map_comp; apply/eq_in_map => i /=; rewrite -iterSr.
by apply/mapP => /= -[] [| i]; rewrite mem_iota // => H /eqP;
   rewrite iter_invariance //; apply/negP; elim/path_ind: x xs / Hxs H.
Qed.

Lemma connect_findeq y : connect x y -> find x = find y.
Proof. by move => /iter_findex <-; rewrite iter_find. Qed.

End wacycle.

Lemma step_wacycle x : wacycle (g x) = wacycle x.
Proof.
apply/eqP/eqP; rewrite -!iterSr (iterS _.+1); last by move => {2}<-.
have/trajectP [i Hi -> H]: iter #|T|.+1 g x \in orbit g x by
  rewrite -fconnect_orbit fconnect_iter.
suff/subnK <- : i <= #|T| by rewrite iter_add; elim: (#|T| - i) => //= i' ->.
by apply/ltnW/(leq_trans Hi)/subset_leq_card/subsetP.
Qed.

Lemma iter_wacycle n x : wacycle (iter n g x) = wacycle x.
Proof. by elim: n => //= n <-; rewrite step_wacycle. Qed.

Lemma connect_wacycle x y : connect x y -> wacycle x = wacycle y.
Proof. by move/iter_findex <-; rewrite iter_wacycle. Qed.

End static.

Notation find g := (iter #|T| g).

Section dynamic.

Variable (g : G).

Lemma subst_wacycle x y z :
  ~~ connect g z x -> wacycle (ffun_subst g x y) z = wacycle g z.
Proof.
set g' := ffun_subst g x y => Hzx; rewrite /wacycle iterS ffunE.
suff ->: find g' z = find g z
  by case: (_ =P x) Hzx => [<- |]; rewrite ?connect_iter.
by elim: #|T| z Hzx => //= n IH z Hzx;
  rewrite !ffunE IH //; case: eqP Hzx => // <-; rewrite connect_iter.
Qed.

Lemma find_subst_separated x y z :
  ~~ connect g z x -> find (ffun_subst g x y) z = find g z.
Proof.
by elim: #|T| z => //= n IH z Hzx;
  rewrite ffunE IH //; case: (_ =P x) Hzx => // <-; rewrite connect_iter.
Qed.

Variable (Hg : acycle g).

Lemma subst_acycle x y : ~~ connect g y x -> acycle (ffun_subst g x y).
Proof.
set g' := ffun_subst g x y => Hyx z.
case: (boolP (connect g z x)) => Hzx; last by rewrite subst_wacycle.
suff/connect_wacycle ->: connect g' z x
  by rewrite -step_wacycle ffunE eqxx subst_wacycle.
case/connectP: Hzx => zs Hzs Hx; subst x; apply/connectP; exists zs => //.
subst g'; elim/path_ind: z zs / Hzs Hyx => //= z zs H Hzs IH H0.
rewrite ffunE H IH // !andbT; suff/negbTE ->: z != last (g z) zs by [].
have/(path_notin (Hg _)): path g z (g z :: zs) by rewrite /= eqxx H.
by apply/contra => /eqP {1}->; rewrite mem_last.
Qed.

Lemma find_subst_graft x y :
  ~~ findeq g x y -> find (ffun_subst g (find g x) y) x = find g y.
Proof.
rewrite /findeq; case/connectP: (connect_find g x) => xs Hxs H Hxy; rewrite H.
elim/path_ind: x xs / Hxs Hxy H => /= [x Hxy _ | x xs H _ H0 H1 H2].
- have {Hxy} Hxy: ~~ connect g y x by apply/contra: Hxy => /connect_findeq ->.
  rewrite -step_find; first by rewrite ffunE eqxx find_subst_separated.
  by rewrite -step_wacycle ffunE eqxx subst_wacycle.
- rewrite -step_find;
    first by rewrite ffunE -{2}H2 find_invariance // (negbTE H) H0 // step_find.
  by apply/subst_acycle; apply/contra: H1
    => /connect_findeq -> //; rewrite -H2 findI.
Qed.

Lemma find_subst x y z :
  ~~ findeq g x y -> find (ffun_subst g (find g x) y) z =
                     find g (if findeq g z x then y else z).
Proof.
by rewrite /findeq; case: (altP (find g z =P _)) => [<- Hzy | Hzx Hxy];
   rewrite (find_subst_graft, find_subst_separated) //;
   apply/contra: Hzx => /connect_findeq -> //; rewrite findI.
Qed.

End dynamic.

(* Monadic definition of union-find and its properties *)
Section monadic.

Fixpoint mfind_rec n x : AState [:: (T, T : Type)] T :=
  if n is n'.+1
  then x' <- astate_get x;
       if x == x'
       then astate_ret x
       else mfind_rec n' x'
  else astate_ret x.

Definition mfind := mfind_rec #|T|.

Definition munion x y : AState [:: (T, nat : Type); (T, T : Type)] unit :=
  x' <- astate_lift (mfind x);
  y' <- astate_lift (mfind y);
  if x' == y' then astate_ret tt else
  wx <- astate_get x';
  wy <- astate_get y';
  if wx <= wy
    then astate_lift (astate_put x' y');; astate_put y' (wx + wy)
    else astate_lift (astate_put y' x');; astate_put x' (wx + wy).

Variable (g : G) (w : Gw) (Hg : acycle g).

Lemma run_mfind x : run_AState (mfind x) g = (find g x, g).
Proof.
rewrite /mfind; elim: #|T| x => //= n IH x; case: eqP => H /=;
  by [congr pair; elim: n {IH} => //= n <- | rewrite IH -iterSr].
Qed.

Lemma munion_acycle x y : acycle (run_AState (munion x y) w g).2.
Proof.
by rewrite /= !run_mfind /=; case: (altP eqP) => //= H; case: leqP => /= _;
  apply subst_acycle => //; apply/contra: H => /connect_findeq;
  rewrite !findI // => ->.
Qed.

Lemma munion_findeq x y a b :
  findeq (run_AState (munion x y) w g).2 a b =
  findeq g a b || findeq g a x && findeq g b y || findeq g a y && findeq g b x.
Proof.
rewrite /= !run_mfind /=; case: (altP eqP) => /=; rewrite /findeq;
  [ do !case: eqP => //=; congruence | case: leqP => /= _ H ];
  rewrite !(@find_subst _ Hg x (find g y), @find_subst _ Hg y (find g x))
          /findeq ?findI // 1?eq_sym // !(fun_if (iter _ _)) findI //;
  move/eqP: H; do! case: eqP => //=; congruence.
Qed.

End monadic.



End union_find.
End union_find.
