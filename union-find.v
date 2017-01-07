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

Definition ffun_subst (I : finType) (T : Type) i x (f : {ffun I -> T}) :=
  [ffun j => if j == i then x else f j].

Lemma subst_id (I : finType) (T : Type) (f : {ffun I -> T}) i x :
  x = f i -> ffun_subst i x f = f.
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
    (fun I T sig i x a => run_AState_ret sig (tt, ffun_subst i x a)).

Canonical AState_monadType sig :=
  @MonadType (AState sig) (runt_AState sig)
             (@run_AState sig) (@astate_ret sig) (@astate_bind sig).

(******************************************************************************)
(* Union-find                                                                 *)
(******************************************************************************)

Module union_find.
Section union_find.

Variable (T : finType) (R : eqType) (Ridx : R) (Rop : Monoid.com_law Ridx).
Definition G := {ffun T -> T + R}.

Section static.

Variable (g : G).

Definition succ x := if g x is inl x' then x' else x.
Definition classval x := if g x is inr a then a else Ridx.
Definition repr x := g x == inr (classval x).

Definition path := path (fun x y => g x == inl y).
Definition connect := fconnect succ.

Lemma path_ind (P : T -> seq T -> Prop)
  (Hnil : forall x, P x [::])
  (Hcons : forall x xs, ~~ repr x -> path (succ x) xs ->
                        P (succ x) xs -> P x (succ x :: xs))
  x xs : path x xs -> P x xs.
Proof.
elim: xs x => //= x' xs IH x /andP [] /eqP H H0.
have Hx': x' = succ x by rewrite /succ H.
by subst x'; apply Hcons; auto; rewrite /repr H /eq_op.
Qed.

Lemma connectP (x y : T) :
  reflect (exists2 p : seq T, path x p & y = last x p) (connect x y).
Proof.
apply: (iffP idP); last by case => xs Hxs ->; apply/connectP; exists xs => //;
                           elim/path_ind: x xs / Hxs => //= ?; rewrite eqxx.
rewrite /connect fconnect_orbit => H; apply/connectP.
move: (orbit_uniq succ x) H; rewrite /orbit.
move: (order _ _) => n; elim: n x => //= n IH x.
case/andP => H H0; rewrite inE => /orP [/eqP -> | H1]; first by apply connect0.
case: n IH H H0 H1 => // n IH H H0 H1.
apply connect_trans with (succ x); last by apply IH.
by rewrite /succ; case_eq (g x) => x' Hx';
   [ apply/connect1/eqP | apply connect0 ].
Qed.

(*
Lemma connectP' (x y : T) :
  reflect (exists2 i : nat, i < order succ x & y = iter i succ x) (connect x y).
Proof.
apply (iffP idP); last by case => i H -> {y}; apply fconnect_iter.
by rewrite /connect fconnect_orbit /orbit => /trajectP [] i H -> {y}; exists i.
Qed.
*)

Arguments connectP [x y].

Notation find x := (iter #|T| succ x).
Definition findeq x y := find x == find y.

Definition wacycle x := repr (find x).
Definition acycle := forall x, wacycle x.

Lemma connect1 x : connect x (succ x). Proof. by apply fconnect1. Qed.

Lemma connect_iter n x : connect x (iter n succ x).
Proof. by apply fconnect_iter. Qed.

Lemma connect_find x : connect x (find x).
Proof. by rewrite connect_iter. Qed.

Lemma reprP x : reflect (exists x', g x = inr x') (repr x).
Proof.
by rewrite /repr /classval; case: (g x) => x'; rewrite ?eqxx /eq_op /=;
   constructor; [case => ?; congruence | exists x'].
Qed.

Lemma repr_iter n x : repr x -> repr (iter n succ x).
Proof.
case/reprP => a H; apply/reprP; exists a.
by elim: n => //= n {H} H; rewrite {1}/succ !H.
Qed.

Lemma full_path_connect x xs :
  path x xs -> repr (last x xs) -> x :: xs =i connect x.
Proof.
move => H H0 y; apply/idP/connectP => [H1 | [xs' H1 H2]];
  first by case: {H1} (splitPl H1) H H0 => xs1 xs2;
    rewrite /path cat_path last_cat /= -!/(path _ _) => Hy /andP [] H H0 H1;
    subst y; exists xs1.
subst y; elim/path_ind: x xs' / H1 xs H H0;
  first by move => *; apply/orP/or_introl.
move => /= x' xs' H Hxs' IH xs Hxs H0; rewrite inE; apply/orP/or_intror.
elim/path_ind: x' xs / Hxs Hxs' IH H H0 => [x' |]; auto.
by rewrite /repr /succ; case: (g x') => //= b _ _ /negbTE ->.
Qed.

Section wacycle.

Variables (x : T) (Hx : wacycle x).

Lemma find_succ : succ (find x) = find x.
Proof. by rewrite {1}/succ; case/reprP: Hx => x' ->. Qed.

Lemma succ_find : find (succ x) = find x.
Proof. by rewrite -iterSr /= find_succ. Qed.

Lemma find_iter n : iter n succ (find x) = find x.
Proof. by elim: n => // n IH; rewrite iterSr find_succ IH. Qed.

Lemma iter_find n : find (iter n succ x) = find x.
Proof. by rewrite -iter_add addnC iter_add find_iter. Qed.

Lemma findI : find (find x) = find x. Proof. by rewrite find_iter. Qed.

Lemma iter_invariance n : 0 < n -> (x == iter n succ x) = (x == succ x).
Proof.
case: n => // n _; apply/eqP/eqP => H; last by elim: n => //= n <-.
suff ->: x = iter (#|T| * n.+1) succ x
  by rewrite -iterS mulnS -addnS !(addnC #|T|) !iter_add !find_iter.
by elim: #|T| => // c IH; rewrite mulSn iter_add -IH -H.
Qed.

Lemma find_invariance : (x == find x) = (x == succ x).
Proof. by rewrite iter_invariance //; apply/card_gt0P; exists x. Qed.

Lemma reprE : repr x = (x == succ x).
Proof.
apply/idP/idP; first by rewrite /succ; case/reprP => x' ->.
by rewrite -find_invariance => /eqP H; move: Hx; rewrite /wacycle -H.
Qed.

Lemma path_notin xs : path x xs -> x \notin xs.
Proof.
move => Hxs; have ->: xs = [seq iter i succ x | i <- iota 1 (size xs)] by
  elim/path_ind: x xs / Hxs => //= x' xs H Hxs {1}->; congr cons;
  rewrite (iota_addl 1 1) -map_comp; apply/eq_in_map => i /=; rewrite -iterSr.
apply/mapP => /= -[] [| i]; rewrite mem_iota add1n // => H /eqP.
rewrite iter_invariance // -find_invariance => /eqP H0.
by move: Hx; rewrite /wacycle -H0 {H0}; apply/negP; elim/path_ind: x xs / Hxs H.
Qed.

Lemma connect_findeq y : connect x y -> find x = find y.
Proof. by move => /iter_findex <-; rewrite iter_find. Qed.

End wacycle.

Lemma wacycle_repr x : repr x -> wacycle x.
Proof.
rewrite /wacycle => H; suff <-: x = iter #|T| succ x by [].
by elim: #|T| => //= n <-; move/eqP: H; rewrite /succ => ->.
Qed.

Lemma wacycle_succ x : wacycle (succ x) = wacycle x.
Proof.
apply/reprP/reprP; case => x' H; exists x';
  [ move: H; rewrite -iterSr | by rewrite -iterSr /= {1}/succ !H].
have/trajectP [i Hi -> H] : iter #|T|.+1 succ x \in orbit succ x
  by rewrite -fconnect_orbit fconnect_iter.
have/subnK <- : i <= #|T| by apply/ltnW/(leq_trans Hi)/subset_leq_card/subsetP.
by rewrite iter_add; elim: (#|T| - i) => //= i' IH; rewrite {1}/succ IH.
Qed.

Lemma wacycle_iter n x : wacycle (iter n succ x) = wacycle x.
Proof. by elim: n => //= n <-; rewrite wacycle_succ. Qed.

Lemma wacycle_connect x y : connect x y -> wacycle x = wacycle y.
Proof.  by move/iter_findex <-; rewrite wacycle_iter. Qed.

Lemma repr_find x : wacycle x -> repr (find x).
Proof. by move => H; rewrite reprE ?wacycle_iter // find_succ. Qed.

Lemma path_uniq x xs : wacycle x -> path x xs -> uniq (x :: xs).
Proof.
move => H H0; elim/path_ind: x xs / H0 H => //= x xs H Hxs IH Hx.
by rewrite IH ?wacycle_succ // path_notin //= Hxs; move: H;
   rewrite /repr /classval /succ; case_eq (g x) => x'; rewrite !eqxx.
Qed.

Lemma iter_findeq x y m n :
  wacycle x -> iter m succ x = iter n succ y -> find x = find y.
Proof.
by move => Hx Hy; move: (Hx);
  rewrite -(wacycle_iter m x) -(iter_find Hx m) {}Hy wacycle_iter => /iter_find.
Qed.

Lemma path_size x xs : wacycle x -> path x xs -> size xs < #|T|.
Proof. by move => H /(path_uniq H) /card_uniqP /= <-; apply max_card. Qed.

End static.

Arguments connectP [g x y].

Notation find g := (@iter T #|T| (succ g)).

Section dynamic.

Variable (g : G).

Definition compress x :=
  [ffun y => if (y \in orbit (succ g) x) && (y != find g x)
             then inl (find g x) else g y].

Lemma find_subst_separated x y y' :
  ~~ connect g x y -> find (ffun_subst y y' g) x = find g x.
Proof.
elim: #|T| x => //= n IH x Hxy; rewrite !/(succ _ _) ffunE IH //.
by case: (_ =P y) Hxy => // <-; rewrite connect_iter.
Qed.

Lemma wacycle_subst x y y' :
  ~~ connect g x y -> wacycle (ffun_subst y y' g) x = wacycle g x.
Proof.
by move => Hxy; rewrite /wacycle find_subst_separated // /repr /classval ffunE;
  case: (_ =P y) Hxy => //= <-; rewrite connect_iter.
Qed.

Lemma wacycle_substR x y a :
  wacycle (ffun_subst x (inr a) g) y = connect g y x || wacycle g y.
Proof.
case: (altP connectP) => /=; last apply wacycle_subst.
case => ys Hys Hx; subst x.
elim/path_ind: y ys / Hys => [y | y ys H Hys] /=;
  first by apply/repr_iter/reprP; rewrite ffunE eqxx; exists a.
rewrite -(wacycle_succ _ y) /(succ (ffun_subst _ _ _)) ffunE; case: eqP => //.
move: H Hys.
rewrite /repr /classval /succ; case_eq (g y) => // y' H H0 H1 H2 _; subst y.
by apply wacycle_repr; rewrite /repr /classval ffunE eqxx.
Qed.

Lemma path_subst_separated x y z xs :
  ~~ connect g x y -> path (ffun_subst y z g) x xs = path g x xs.
Proof.
elim: xs x => //= x' xs IH x H; rewrite /succ ffunE.
have/negbTE ->: x != y by apply/contra: H => /eqP ->; apply connect0.
case: eqP => //= H0; apply IH; apply/contra/connect_trans: H.
by have ->: x' = succ g x; [ rewrite /succ H0 | apply connect1 ].
Qed.

Lemma path_subst_graft x y xs :
  wacycle g x -> ~~ connect g x y ->
  path g x xs -> path (ffun_subst (last x xs) (inl y) g) x (rcons xs y).
Proof.
move => H H0 H1.
elim/path_ind: x xs / H1 H H0 => /= [x H H0 | x xs H H0 H1 H2 H3];
  rewrite ffunE ?eqxx //.
have H4: g x == inl (succ g x)
  by move: H; rewrite /repr /classval /succ; case: (g x) => x'; rewrite ?eqxx.
have/(path_notin H2): path g x (succ g x :: xs) by rewrite /= H0 andbT.
case: (x =P last _ _) => [{1}-> | _ _]; first by rewrite mem_last.
by rewrite H4 /= H1 ?wacycle_succ //; apply/contra/connect_trans/connect1: H3.
Qed.

Lemma repr_compress x y : repr g y = repr (compress x) y.
Proof.
rewrite /repr /classval /compress !ffunE /(succ _ _).
case: ifP; case_eq (g y) => // b Hy' /andP [] /trajectP [i Hi Hy] /negP [].
move/ltnW/subnK: (leq_trans Hi (max_card _)) => <-.
by rewrite iter_add -Hy; apply/eqP;
   elim: (#|T| - i) => //= {i Hi Hy} i <-; rewrite /succ Hy'.
Qed.

Lemma path_compress x y xs :
  wacycle g x -> path g x xs -> ~~ connect g y (last x xs) ->
  path (compress y) x xs.
Proof.
move => H H0; elim/path_ind: x xs / H0 H => //= x xs H Hxs IH H0 H1.
rewrite {}IH // ?wacycle_succ // andbT ffunE.
case: (altP andP) => [[] H2 |];
  last by move: H; rewrite /repr /classval /(succ _ _);
          case: (g x) => x'; rewrite eqxx.
case/trajectP: H2 Hxs H H0 H1 => i Hi ->; rewrite wacycle_iter => Hxs H H0 H1.
by case/negP: H1; apply connect_trans with (iter i.+1 (succ g) y);
   rewrite -/(connect _) ?connect_iter //=; apply/connectP; exists xs.
Qed.

Lemma succ_compress x y :
  wacycle g x ->
  succ (compress y) x = if connect g y x then find g y else succ g x.
Proof.
by move => H; rewrite /(succ _ _) ffunE; case: (altP andP); case: ifP => // H0;
  rewrite -fconnect_orbit -/(connect _) H0 /= ?negbK -/(succ _ _);
  [ case | move/eqP => ->; rewrite find_succ // (wacycle_connect H0) ].
Qed.

Lemma compress_repr x y : repr g x -> compress y x = inr (classval g x).
Proof.
rewrite /repr /classval ffunE; case: andP; case_eq (g x) => // a H [] /trajectP
  [i] /ltnW /leq_trans /(_ (max_card _)) /subnK <- Hx /eqP []; subst x.
by rewrite iter_add; elim: (#|T| - i) => //= j <-; rewrite /(succ _ _) H.
Qed.

Lemma find_compress x y : wacycle g x -> find (compress y) x = find g x.
Proof.
move => H.
suff [i /subnK <- ->]:
  exists2 i, #|T| <= i & find (compress y) x = iter i (succ g) x
  by rewrite iter_add /= find_iter.
elim: #|T|; [ exists 0 | ] => //= i [j Hj] ->;
  rewrite succ_compress ?wacycle_iter //; case: ifP => H0; last by exists j.+1.
exists (maxn #|T| j.+1); first by rewrite leq_max ltnS Hj orbT.
by rewrite maxnE iter_add iter_find // (connect_findeq _ H0) ?iter_find //
           (wacycle_connect H0) wacycle_iter.
Qed.

Lemma wacycle_compress x y : wacycle g x -> wacycle (compress y) x.
Proof.
by move => H; rewrite /wacycle /repr /classval find_compress // compress_repr.
Qed.

Variable (Hg : acycle g).

Lemma acycle_substL x y : ~~ connect g y x -> acycle (ffun_subst x (inl y) g).
Proof.
set g' := ffun_subst x (inl y) g => Hyx z.
case: (boolP (connect g z x)) => Hzx; last by rewrite wacycle_subst.
suff/wacycle_connect ->: connect g' z x
  by rewrite -wacycle_succ /succ ffunE eqxx wacycle_subst.
case/connectP: Hzx => zs Hzs Hx; subst x; apply/connectP; exists zs => //.
subst g'; elim/path_ind: z zs / Hzs Hyx => //= z zs H Hzs IH H0.
move: H Hzs; rewrite IH // {IH H0} andbT /repr /classval /succ ffunE.
case_eq (g z) => z'; rewrite ?eqxx // => Hz H Hzs.
suff/negbTE ->: z != last z' zs by [].
have/(path_notin (Hg _)): path g z (z' :: zs) by rewrite /= Hz eqxx.
by apply/contra => /eqP {1}->; rewrite mem_last.
Qed.

Lemma find_substL_graft x y :
  ~~ findeq g x y -> find (ffun_subst (find g x) (inl y) g) x = find g y.
Proof.
rewrite /findeq; case/connectP: (connect_find g x) => xs Hxs H Hxy; rewrite H.
elim/path_ind: x xs / Hxs Hxy H => /= [x H _ | x xs H _ H0 H1 H2];
  [have {H} H: ~~ connect g y x by apply/contra: H => /connect_findeq -> |];
  rewrite -succ_find.
- by rewrite /(succ _ _) ffunE eqxx find_subst_separated.
- by rewrite -wacycle_succ /(succ _ _) ffunE eqxx wacycle_subst.
- by rewrite /(succ (ffun_subst _ _ _) _) ffunE -{2}H2 find_invariance //
             -reprE // (negbTE H) -/(succ _ _) H0 // succ_find.
- by apply/acycle_substL; apply/contra: H1 => /connect_findeq -> //;
     rewrite -H2 findI.
Qed.

Lemma find_substL x y z :
  ~~ findeq g x y -> find (ffun_subst (find g x) (inl y) g) z =
                     find g (if findeq g z x then y else z).
Proof.
by rewrite /findeq; case: (altP (find g z =P _)) => [<- Hzy | Hzx Hxy];
   rewrite (find_substL_graft, find_subst_separated) //;
   apply/contra: Hzx => /connect_findeq -> //; rewrite findI.
Qed.

Lemma acycle_compress x : acycle (compress x).
Proof. by move => y; apply wacycle_compress. Qed.

End dynamic.

(* Monadic definition of union-find and its properties *)
Section monadic.

Variable (cmp : R -> R -> bool).

Section find.

Variable (g : G) (Hg : acycle g).

Fixpoint mfind_rec n x : AState [:: (T, (T + R)%type)] (T * R) :=
  if n is n'.+1
  then x' <- astate_get x;
       match x' with
         | inl x'' =>
           r <- mfind_rec n' x'';
           astate_put x (inl r.1);;
           astate_ret r
         | inr a => astate_ret (x, a)
       end
  else astate_ret (x, Ridx).

Definition mfind := mfind_rec #|T|.

Lemma run_mfind_rec n x xs :
  let x' := last x xs in
  path g x xs -> size xs < n -> repr g x' ->
  run_AState (mfind_rec n x) g =
  (x', classval g x',
   [ffun z => if (z \in x :: xs) && (z != x') then inl x' else g z]).
Proof.
move => /= H /subnK <-; move: {n} (n - _) => n; rewrite addnC.
elim/path_ind: x xs / H (path_uniq (Hg _) H) => [x /= _ H | x xs];
  first by rewrite (eqP H) /=; congr (_, _, _);
           apply/ffunP => z; rewrite ffunE inE andbN.
rewrite reprE // /(succ g x); case_eq (g x) => x';
  rewrite ?eqxx //= inE negb_or -andbA => H H0 H1 H2 /and4P [_ H3 H4 H5] H6.
rewrite H /= {}H2 ?H4 //=; congr (_, _, _); apply/ffunP => y; rewrite !ffunE.
move/eqP: H6 => H6; rewrite !inE; do !case: eqP => //=; congruence.
Qed.

Lemma run_mfind x :
  run_AState (mfind x) g = (find g x, classval g (find g x), compress g x).
Proof.
case/connectP: (connect_find g x) => xs Hxs H.
have Hrepr: repr g (last x xs) by rewrite -H; apply Hg.
rewrite H /mfind (@run_mfind_rec #|T| x xs) // ?(path_size (Hg _) Hxs) //.
congr (_, _, _); apply/ffunP => y; rewrite !ffunE H;
  congr (if (_ \in _) && _ then _ else _).
rewrite /orbit /order -/(connect _) -(eq_card (full_path_connect Hxs _)) //.
by move/card_uniqP: (path_uniq (Hg _) Hxs) {y Hrepr} => ->;
   congr cons; elim/path_ind: x xs / Hxs {H} => //= x xs _ _ <-.
Qed.

End find.

Section union.

Variable (g : G) (Hg : acycle g).

Definition union x y :=
  let x' := find g x in let y' := find g y in
  let v  := Rop (classval g x') (classval g y') in
  let g' := compress (compress g x) y in
  if x' == y' then g' else
    if cmp (classval g x') (classval g y')
    then ffun_subst y' (inr v) (ffun_subst x' (inl y') g')
    else ffun_subst x' (inr v) (ffun_subst y' (inl x') g').

Definition munion x y : AState [:: (T, (T + R)%type)] unit :=
  x' <- mfind x;
  y' <- mfind y;
  if x'.1 == y'.1 then astate_ret tt else
  if cmp x'.2 y'.2
    then astate_put x'.1 (inl y'.1);;
         astate_put y'.1 (inr (Rop x'.2 y'.2))
    else astate_put y'.1 (inl x'.1);;
         astate_put x'.1 (inr (Rop x'.2 y'.2)).

Lemma run_munion x y : run_AState (munion x y) g = (tt, union x y).
Proof.
rewrite /union /= !run_mfind //=; last by apply acycle_compress.
rewrite find_compress // /(classval (compress _ _)) compress_repr ?repr_find //.
by case: (altP eqP) => //= H; case: (boolP (cmp _ _)).
Qed.

End union.

End monadic.

End union_find.

Section weighted_union.

End weighted_union.

End union_find.
