Require Import all_ssreflect core.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(******************************************************************************)
(* Union-find                                                                 *)
(******************************************************************************)

Section union_find.

Variable (R : eqType) (Ridx : R) (Rop : Monoid.com_law Ridx) (cmp : rel R)
         (T : finType).
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
by subst x'; apply: Hcons; auto; rewrite /repr H /eq_op.
Qed.

Lemma connectP (x y : T) :
  reflect (exists2 p : seq T, path x p & y = last x p) (connect x y).
Proof.
apply: (iffP idP); last by case=> xs Hxs ->; apply/connectP; exists xs => //;
                           elim/path_ind: x xs / Hxs => //= ?; rewrite eqxx.
rewrite /connect fconnect_orbit => H; apply/connectP.
move: (orbit_uniq succ x) H; rewrite /orbit.
move: (order _ _) => n; elim: n x => //= n IH x.
case/andP => H H0; rewrite inE => /orP [/eqP -> | H1]; first exact: connect0.
case: n IH H H0 H1 => // n IH H H0 H1.
apply/connect_trans/(IH (succ x)); rewrite // /succ.
by case_eq (g x) => x' Hx'; [ apply/connect1/eqP | apply: connect0 ].
Qed.

Lemma connectP' (x y : T) :
  reflect (exists2 i : nat, i < order succ x & y = iter i succ x) (connect x y).
Proof.
apply: (iffP idP); last by case=> i H -> {y}; apply: fconnect_iter.
by rewrite /connect fconnect_orbit /orbit => /trajectP [] i H -> {y}; exists i.
Qed.

Arguments connectP [x y].
Arguments connectP' [x y].

Definition find := iter #|T| succ.
Definition findeq x y := find x == find y.

Definition lacycle x := repr (find x).
Definition acycle := forall x, lacycle x.

Lemma connect0 x : connect x x. Proof. exact: connect0. Qed.

Lemma connect1 x : connect x (succ x). Proof. exact: fconnect1. Qed.

Lemma connect_trans x y z : connect x y -> connect y z -> connect x z.
Proof. exact: connect_trans. Qed.

Lemma connectE x y : connect x y = (x == y) || connect (succ x) y.
Proof.
apply/idP/idP => [/connectP [xs Hxs ->] | /orP []].
- by case: xs Hxs; rewrite ?eqxx //= => x' xs /andP [] /eqP H H0;
     rewrite /succ H; apply/orP/or_intror; apply/connectP; exists xs.
- by move/eqP => ->; apply: connect0.
- by apply/connect_trans/connect1.
Qed.

Lemma connect_iter n x : connect x (iter n succ x).
Proof. exact: fconnect_iter. Qed.

Lemma connect_find x : connect x (find x).
Proof. by rewrite connect_iter. Qed.

Lemma connect_succL x y : connect (succ x) y -> connect x y.
Proof. by apply/connect_trans/connect1. Qed.

Lemma connect_succR x y : connect x y -> connect x (succ y).
Proof. by move=> H; apply/(connect_trans H)/connect1. Qed.

Lemma reprP x : reflect (exists x', g x = inr x') (repr x).
Proof.
by rewrite /repr /classval; case: (g x) => x'; rewrite ?eqxx /eq_op /=;
   constructor; [case=> ?; congruence | exists x'].
Qed.

Lemma repr_succ x : repr x -> repr (succ x).
Proof. by move/eqP => H; rewrite /repr /succ !H. Qed.

Lemma repr_iter n x : repr x -> repr (iter n succ x).
Proof. by move=> H; elim: n => //= n; apply: repr_succ. Qed.

Lemma path_traject x xs : path x xs -> x :: xs = traject succ x (size xs).+1.
Proof. by move=> H; elim/path_ind: x xs / H => //= x xs H Hxs [] {1}->. Qed.

Lemma full_path_connect x xs :
  path x xs -> repr (last x xs) -> x :: xs =i connect x.
Proof.
move=> H H0 y; apply/esym.
rewrite unfold_in -/(fingraph.connect _ _ _) -/(connect _ _).
elim/path_ind: x xs / H H0 => /= [x H | x xs H Hxs IH H0];
  last by rewrite inE -IH // connectE eq_sym.
rewrite !inE; apply/idP/eqP => [| ->]; last exact: connect0.
 by case/connectP => -[| x' xs] //= /andP []; rewrite (eqP H) eqE.
Qed.

Section lacycle.

Variables (x : T) (Hx : lacycle x).

Lemma find_succ : succ (find x) = find x.
Proof. by rewrite {1}/succ; case/reprP: Hx => x' ->. Qed.

Lemma succ_find : find (succ x) = find x.
Proof. by rewrite /find -iterSr /= find_succ. Qed.

Lemma find_iter n : iter n succ (find x) = find x.
Proof. by elim: n => // n IH; rewrite iterSr find_succ IH. Qed.

Lemma iter_find n : find (iter n succ x) = find x.
Proof. by rewrite /find -iter_add addnC iter_add find_iter. Qed.

Lemma findI : find (find x) = find x. Proof. by rewrite /find find_iter. Qed.

Lemma iter_invariance n : 0 < n -> (x == iter n succ x) = (x == succ x).
Proof.
case: n => // n _; apply/eqP/eqP => H; last by elim: n => //= n <-.
suff ->: x = iter (#|T| * n.+1) succ x by
  rewrite -iterS mulnS -addnS !(addnC #|T|) !iter_add !find_iter.
by elim: #|T| => // c IH; rewrite mulSn iter_add -IH -H.
Qed.

Lemma find_invariance : (x == find x) = (x == succ x).
Proof. by rewrite iter_invariance //; apply/card_gt0P; exists x. Qed.

Lemma reprE : repr x = (x == succ x).
Proof.
apply/idP/idP; first by rewrite /succ; case/reprP => x' ->.
by rewrite -find_invariance => /eqP H; move: Hx; rewrite /lacycle -H.
Qed.

Lemma path_notin xs : path x xs -> x \notin xs.
Proof.
move=> Hxs; have ->: xs = [seq iter i succ x | i <- iota 1 (size xs)] by
  elim/path_ind: x xs / Hxs => //= x' xs H Hxs {1}->; congr cons;
  rewrite (iota_addl 1 1) -map_comp; apply/eq_in_map => i /=; rewrite -iterSr.
apply/mapP => /= -[] [| i]; rewrite mem_iota add1n // => H /eqP.
rewrite iter_invariance // -find_invariance => /eqP H0.
by move: Hx; rewrite /lacycle -H0 {H0}; apply/negP; elim/path_ind: x xs / Hxs H.
Qed.

Lemma connect_findeq y : connect x y -> find x = find y.
Proof. by move=> /iter_findex <-; rewrite iter_find. Qed.

End lacycle.

Lemma lacycle_repr x : repr x -> lacycle x.
Proof.
rewrite /lacycle => H; suff <-: x = find x by [].
by rewrite /find; elim: #|T| => //= n <-; move/eqP: H; rewrite /succ => ->.
Qed.

Lemma lacycle_succ x : lacycle (succ x) = lacycle x.
Proof.
apply/reprP/reprP; case=> x' H; exists x';
  [ move: H; rewrite /find -iterSr | by rewrite /find -iterSr /= {1}/succ !H].
case/connectP': (connect_iter #|T|.+1 x) => i Hi -> H.
have/subnK <- : i <= #|T| by apply/ltnW/(leq_trans Hi)/subset_leq_card/subsetP.
by rewrite iter_add; elim: (#|T| - i) => //= i' IH; rewrite {1}/succ IH.
Qed.

Lemma lacycle_iter n x : lacycle (iter n succ x) = lacycle x.
Proof. by elim: n => //= n <-; rewrite lacycle_succ. Qed.

Lemma lacycle_find x : lacycle (find x) = lacycle x.
Proof. by rewrite /find lacycle_iter. Qed.

Lemma lacycle_connect x y : connect x y -> lacycle x = lacycle y.
Proof. by move/iter_findex <-; rewrite lacycle_iter. Qed.

Lemma findeq_connect x y : lacycle x -> findeq x y = connect x (find y).
Proof.
move=> H; apply/eqP/idP => [<- |]; first exact: connect_find.
by move/(connect_findeq H) => H0; move: H0 H; rewrite /lacycle => ->;
   rewrite -/(lacycle _) lacycle_find => H; rewrite findI.
Qed.

Lemma path_uniq x xs : lacycle x -> path x xs -> uniq (x :: xs).
Proof.
move=> H H0; elim/path_ind: x xs / H0 H => //= x xs H Hxs IH Hx.
by rewrite IH ?lacycle_succ // path_notin //= Hxs; move: H;
   rewrite /repr /classval /succ; case (g x) => x'; rewrite !eqxx.
Qed.

Lemma iter_findeq x y m n :
  lacycle x -> iter m succ x = iter n succ y -> find x = find y.
Proof.
by move=> Hx Hy; move: (Hx);
  rewrite -(lacycle_iter m x) -(iter_find Hx m) {}Hy lacycle_iter => /iter_find.
Qed.

Lemma path_size x xs : lacycle x -> path x xs -> size xs < #|T|.
Proof. by move=> H /(path_uniq H) /card_uniqP /= <-; apply: max_card. Qed.

End static.

Arguments connectP [g x y].
Arguments connectP' [g x y].

Section dynamic.

Variable (g : G).

Definition compress x :=
  [ffun y => if connect g x y && (y != find g x)
             then inl (find g x) else g y].

Lemma succ_subst x y z :
  succ (ffun_set y z g) x =
  if x == y then (if z is inl z' then z' else x) else succ g x.
Proof. by rewrite /succ ffunE; case: ifP. Qed.

Lemma find_subst_separated x y y' :
  ~~ connect g x y -> find (ffun_set y y' g) x = find g x.
Proof.
by rewrite /find; elim: #|T| x => //= n IH x Hxy;
rewrite succ_subst IH //; case: (_ =P y) Hxy => // <-; rewrite connect_iter.
Qed.

Lemma lacycle_subst_separated x y y' :
  ~~ connect g x y -> lacycle (ffun_set y y' g) x = lacycle g x.
Proof.
by move=> Hxy; rewrite /lacycle find_subst_separated // /repr /classval ffunE;
   case: (_ =P y) Hxy => //= <-; rewrite connect_iter.
Qed.

Lemma lacycle_substR x y a :
  lacycle (ffun_set x (inr a) g) y = connect g y x || lacycle g y.
Proof.
case: (altP connectP) => /=; last apply: lacycle_subst_separated.
case=> ys Hys Hx; subst x.
elim/path_ind: y ys / Hys => [y | y ys H Hys] /=;
  first by apply/repr_iter/reprP; rewrite ffunE eqxx; exists a.
rewrite -(lacycle_succ _ y) succ_subst; case: eqP H Hys => //.
rewrite /repr /classval /succ; case: (g y) => // y' H H0 H1 _; subst y.
by apply: lacycle_repr; rewrite /repr /classval ffunE eqxx.
Qed.

Lemma lacycle_substL x y z :
  lacycle (ffun_set x (inl y) g) z =
  if connect g z x then ~~ connect g y x && lacycle g y else lacycle g z.
Proof.
case: (altP connectP) => [ [] zs Hzs -> {x} | /lacycle_subst_separated -> // ].
apply eq_trans with (lacycle (ffun_set (last z zs) (inl y) g) y);
  first by elim/path_ind: z zs / Hzs => /= [z | z zs H Hzs H0];
           rewrite -lacycle_succ succ_subst ?eqxx //; case: ifP.
move: (last _ _) => {z zs Hzs} x; case: (altP connectP);
  last exact: lacycle_subst_separated.
case=> ys' /shortenP [] ys; rewrite -/(path _) => Hys H _ Hx;
  subst x => {ys'} /=; apply/negbTE.
suff Hys': path (ffun_set (last y ys) (inl y) g) y (rcons ys y) by
  apply/negP => /path_uniq /(_ Hys') /=; rewrite mem_rcons inE eqxx.
rewrite -cats1 /path cat_path -/(path _) /= ffunE !eqxx !andbT.
elim/path_ind: y ys / Hys (inl y) H => // y ys H Hys IH a /andP [H0 H1] /=.
by rewrite IH // andbT ffunE; case: (altP (y =P _)) H0 => [{1}-> | _];
   [ rewrite mem_last | rewrite inE /succ; case (g y) => b; rewrite eqxx ].
Qed.

Lemma lacycle_subst x y z :
  lacycle (ffun_set x y g) z =
  if y is inl y'
    then (if connect g z x
          then ~~ connect g y' x && lacycle g y' else lacycle g z)
    else connect g z x || lacycle g z.
Proof. by case: y => y; rewrite (lacycle_substL, lacycle_substR). Qed.

Lemma find_substR x y a :
  lacycle g x ->
  find (ffun_set y (inr a) g) x = if connect g x y then y else find g x.
Proof.
move=> H; case: (boolP (connect _ _ _)) => H0;
  last by rewrite find_subst_separated.
case/connectP: H0 => xs' /shortenP [xs]; rewrite -/(path _) => Hxs H0 _ ->.
have {H0 Hxs xs'} Hxs: path (ffun_set (last x xs) (inr a) g) x xs by
  elim/path_ind: x xs / Hxs H0 {H} => // x xs H0 Hxs IH /andP [H1 H2] /=;
  rewrite {}IH // andbT ffunE; move: H0 H1; rewrite /repr /classval /succ;
  case: (x =P _); case: (g x) => x'; rewrite ?eqxx //= => ->; rewrite mem_last.
elim: xs x Hxs H => [x _ _ | x' xs IH x /andP []] //=;
  first by rewrite /find; elim: #|T| => //= n ->; rewrite succ_subst eqxx.
rewrite ffunE; case: (altP (x =P _)) => //= H /eqP H0 H1 H2; move: (H2).
rewrite -lacycle_succ /succ H0 => H2'.
by rewrite -{2}IH // -succ_find ?lacycle_subst ?H2 ?orbT //
           succ_subst (negbTE H) /succ H0.
Qed.

Lemma connect_substL x y z :
  connect (ffun_set y (inl z) g) x z = connect g x y || connect g x z.
Proof.
apply/idP/idP =>
  [/connectP [] xs Hxs Hz | /orP [] /connectP [] xs' /shortenP [xs]].
- by subst z; elim: xs x Hxs => /= [x _ | x' xs IH x /andP []];
     rewrite ?(connect0, orbT) // ffunE; case: (altP (x =P y)) => [-> |];
     rewrite ?connect0 // => H /eqP H0 /IH /orP [] H1; apply/orP;
     [left | right]; apply: connect_succL; rewrite /succ H0.
- rewrite -/(path _) => Hxs Hxs' _ -> {y xs'}.
  apply/connect_trans/(connect_succL (x := last x xs));
    last by rewrite succ_subst eqxx connect0.
  elim/path_ind: x xs / Hxs Hxs' => [* | x xs _ _ IH /andP [H] /IH {IH} /=];
    first exact: connect0.
  by apply: connect_trans; apply: connect_succL; rewrite succ_subst;
    case: eqP H => [{1}-> | *]; rewrite (mem_last, connect0).
- rewrite -/(path _) => Hxs Hxs' _ -> {z xs'}.
  elim/path_ind: x xs / Hxs Hxs' => [* | x xs H _ IH /andP [H0] /IH {IH} H1];
    first exact: connect0.
  by apply: connect_succL; rewrite succ_subst; case: eqP => *;
    [ apply: connect0 | apply: H1 ].
Qed.

Lemma path_subst_separated x y z xs :
  ~~ connect g x y -> path (ffun_set y z g) x xs = path g x xs.
Proof.
elim: xs x => //= x' xs IH x H; rewrite ffunE.
have/negbTE ->: x != y by apply/contra: H => /eqP ->; apply: connect0.
case: eqP => //= H0; apply: IH; apply/contra/connect_trans/connectP: H.
by exists [:: x']; rewrite //= H0 eqxx.
Qed.

Lemma path_subst_graft x y xs :
  lacycle g x -> ~~ connect g x y ->
  path g x xs -> path (ffun_set (last x xs) (inl y) g) x (rcons xs y).
Proof.
move=> H H0 H1.
elim/path_ind: x xs / H1 H H0 => /= [x H H0 | x xs H H0 H1 H2 H3];
  rewrite ffunE ?eqxx //.
have H4: g x == inl (succ g x) by
  move: H; rewrite /repr /classval /succ; case: (g x) => x'; rewrite ?eqxx.
have/(path_notin H2): path g x (succ g x :: xs) by rewrite /= H0 andbT.
case: (x =P last _ _) => [{1}-> | _ _]; first by rewrite mem_last.
by rewrite H4 /= H1 ?lacycle_succ //; apply/contra/connect_trans/connect1: H3.
Qed.

Lemma repr_compress x y : repr g y = repr (compress x) y.
Proof.
rewrite /repr /classval /compress !ffunE /(succ _ _).
case: ifP; case_eq (g y) => // b Hy' /andP [] /connectP' [i Hi Hy] /negP [].
rewrite /find; move/ltnW/subnK: (leq_trans Hi (max_card _)) => <-.
by rewrite iter_add -Hy; apply/eqP;
   elim: (#|T| - i) => //= {i Hi Hy} i <-; rewrite /succ Hy'.
Qed.

Lemma path_compress x y xs :
  lacycle g x -> path g x xs -> ~~ connect g y (last x xs) ->
  path (compress y) x xs.
Proof.
move=> H H0; elim/path_ind: x xs / H0 H => //= x xs H Hxs IH H0 H1.
rewrite {}IH // ?lacycle_succ // andbT ffunE.
case: (altP andP) => [[] H2 |];
  last by move: H; rewrite /repr /classval /(succ _ _);
          case: (g x) => x'; rewrite eqxx.
case/connectP': H2 Hxs H H0 H1 => i Hi ->; rewrite lacycle_iter => Hxs H H0 H1.
by case/negP: H1; apply connect_trans with (iter i.+1 (succ g) y);
   rewrite ?connect_iter //=; apply/connectP; exists xs.
Qed.

Lemma succ_compress x y :
  lacycle g x ->
  succ (compress y) x = if connect g y x then find g y else succ g x.
Proof.
by move=> H; rewrite /succ ffunE;
   case: (boolP (connect g y x)) => //=; case: eqP => //= H0;
   rewrite -/(succ _ _) H0; rewrite find_succ // -lacycle_find -H0.
Qed.

Lemma compress_repr x y : repr g x -> compress y x = inr (classval g x).
Proof.
rewrite /repr /classval ffunE /find; case: andP;
  case_eq (g x) => // a H [] /connectP' [i] /ltnW /leq_trans /(_ (max_card _))
                   /subnK <- Hx /eqP []; subst x.
by rewrite iter_add; elim: (#|T| - i) => //= j <-; rewrite /(succ _ _) H.
Qed.

Lemma find_compress x y : lacycle g x -> find (compress y) x = find g x.
Proof.
move=> H.
suff [i /subnK <- ->]:
  exists2 i, #|T| <= i & find (compress y) x = iter i (succ g) x
  by rewrite iter_add /= find_iter.
rewrite /find; elim: #|T|; [ exists 0 | ] => //= i [j Hj] ->;
  rewrite succ_compress ?lacycle_iter //; case: ifP => H0; last by exists j.+1.
exists (maxn #|T| j.+1); first by rewrite leq_max ltnS Hj orbT.
by rewrite maxnE iter_add -/(find _ _) iter_find // (connect_findeq _ H0)
           ?iter_find // (lacycle_connect H0) lacycle_iter.
Qed.

Lemma connect_compress x y z : connect (compress z) x y -> connect g x y.
Proof.
case/connectP => xs Hxs ->;
  elim/path_ind: x xs / Hxs => [| x xs H]; first exact: connect0.
rewrite /(succ _ _) ffunE /=; case: (altP andP);
  last by rewrite -/(succ g x) => H0 H1; apply: connect_succL.
by case: xs => [[] H0 _ | x' xs [] H0] _ _ /=; [ | apply: connect_trans ];
   case/connectP': H0 => i /ltnW /leq_trans /(_ (max_card _)) /subnK Hi ->;
   rewrite /find -Hi iter_add; elim: (#|T| - i); try apply: connect0;
   move=> n H0; apply/(connect_trans H0)/connect1.
Qed.

Lemma lacycle_compress x y : lacycle g x -> lacycle (compress y) x.
Proof.
by move=> H; rewrite /lacycle /repr /classval find_compress // compress_repr.
Qed.

Variable (Hg : acycle g).

Lemma acycle_substL x y z :
  lacycle (ffun_set x (inl y) g) z = ~~ (connect g z x && connect g y x).
Proof. by rewrite lacycle_subst !Hg andbT; case: connect. Qed.

Lemma acycle_substR x a : acycle (ffun_set x (inr a) g).
Proof. by move=> y; rewrite lacycle_subst Hg orbT. Qed.

Lemma find_substL_graft x y :
  ~~ connect g y (find g x) ->
  find (ffun_set (find g x) (inl y) g) x = find g y.
Proof.
case/connectP: (connect_find g x) => xs' /shortenP [xs];
  rewrite -/(path _) => Hxs H _ -> H0 {xs'}.
elim/path_ind: x xs / Hxs H H0 => /= [x _ H0 | x xs H Hxs IH /andP [] H0 H1 H2];
  first by rewrite -succ_find ?lacycle_subst ?connect0 ?H0 //=
                   /succ ffunE eqxx find_subst_separated.
rewrite -{}IH // -succ_find; last by rewrite lacycle_subst H2 andTb; case: ifP.
by rewrite !/(succ _ _) ffunE; case: eqP H0 => [{1}-> | _ H0];
  [ rewrite mem_last | case: (g x) ].
Qed.

Lemma find_substL x y z :
  ~~ connect g y (find g x) -> find (ffun_set (find g x) (inl y) g) z =
                               find g (if findeq g z x then y else z).
Proof.
by rewrite /findeq; case: (altP (find g z =P _)) => [<- Hzy | Hzx Hxy];
   rewrite (find_substL_graft, find_subst_separated) //;
   apply/contra: Hzx => /connect_findeq -> //; rewrite findI.
Qed.

Lemma acycle_compress x : acycle (compress x).
Proof. by move=> y; apply: lacycle_compress. Qed.

End dynamic.

(* Monadic definition of union-find and its properties *)
Section monadic.

Section find.

Variable (g : G) (Hg : acycle g).

Fixpoint mfind_rec n x : AState {ffun T -> T + R} (T * R) :=
  if n is n'.+1
  then mlet x' := astate_get x in
       match x' with
         | inl x'' =>
           mlet '((rep, _) as r) := mfind_rec n' x'' in
           astate_set x (inl rep);;
           astate_ret r
         | inr a => astate_ret (x, a)
       end
  else astate_ret (x, Ridx).

Definition mfind := mfind_rec $|T|.

Lemma run_mfind_rec n x xs :
  let x' := last x xs in
  path g x xs -> size xs < n -> repr g x' ->
  run_AState (mfind_rec n x) g =
  (x', classval g x',
   [ffun z => if (z \in x :: xs) && (z != x') then inl x' else g z]).
Proof.
move=> /= H /subnK <-; move: {n} (n - _) => n; rewrite addnC.
elim/path_ind: x xs / H (path_uniq (Hg _) H) => [x /= _ H | x xs];
  first by rewrite !(run_AStateE, eqP H); congr (_, _);
           apply/ffunP => z; rewrite ffunE inE andbN.
rewrite reprE // /(succ g x); case_eq (g x) => x';
  rewrite ?eqxx //= inE !run_AStateE negb_or -andbA
    => H H0 H1 H2 /and4P [_ H3 H4 H5] H6.
rewrite H !run_AStateE {}H2 ?H4 //= !run_AStateE.
congr (_, _); apply/ffunP => y; rewrite !ffunE.
move/eqP: H6 => H6; rewrite !inE; do !case: eqP => //=; congruence.
Qed.

Lemma run_mfind x :
  run_AState (mfind x) g = (find g x, classval g (find g x), compress g x).
Proof.
case/connectP: (connect_find g x) => xs Hxs H.
have Hrepr: repr g (last x xs) by rewrite -H; apply: Hg.
rewrite H /mfind -cardT' (@run_mfind_rec #|T| x xs) //
        ?(path_size (Hg _) Hxs) //.
congr (_, _, _); apply/ffunP => y; rewrite !ffunE H /connect fconnect_orbit.
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
  if findeq g x y then g' else
    if cmp (classval g x') (classval g y')
    then ffun_set y' (inr v) (ffun_set x' (inl y') g')
    else ffun_set x' (inr v) (ffun_set y' (inl x') g').

Definition munion x y : AState {ffun T -> T + R} unit :=
  mlet '(xr, xv) := mfind x in
  mlet '(yr, yv) := mfind y in
  if xr == yr then astate_ret tt else
  if cmp xv yv
    then astate_set xr (inl yr);; astate_set yr (inr (Rop xv yv))
    else astate_set yr (inl xr);; astate_set xr (inr (Rop xv yv)).

Lemma run_munion x y : run_AState (munion x y) g = (tt, union x y).
Proof.
rewrite /union /findeq !(run_AStateE, run_mfind) //;
  last exact: acycle_compress.
by rewrite find_compress // /(classval (compress _ _)) compress_repr;
  [ do ?case: ifP; rewrite !run_AStateE | apply: Hg ].
Qed.

Lemma union_findeq x y a b :
 findeq (union x y) a b =
  [||findeq g a b, findeq g a x && findeq g b y | findeq g a y && findeq g b x].
Proof.
rewrite /union /findeq; case: ifP => [| /negbT H];
  first by rewrite !find_compress ?lacycle_compress // => /eqP ->;
           apply/idP/idP => [-> | /or3P []] // /andP [] /eqP -> /eqP ->.
set g' := compress (compress g x) y.
have Hg1: acycle g' by move=> z; rewrite !lacycle_compress.
have Hg2 z: find g z = find g' z by rewrite !(find_compress, lacycle_compress).
have Hxy: ((~~ connect g' (find g x) (find g y)) *
           (~~ connect g' (find g y) (find g x)))%type by
  split; apply/contra: H => /connect_findeq;
  rewrite !(lacycle_compress, find_compress, findI) // => ->.
case: ifP => _;
  rewrite !find_substR ?Hg2 ?find_substL
          ?(lacycle_subst, (fun z => esym (Hg2 z)), Hg1, Hxy, if_same) //
          !Hg2 !connect_substL -!findeq_connect // /findeq;
  do !case: (find _ _ =P find _ _) => //=; congruence.
Qed.

End union.

End monadic.

End union_find.

(******************************************************************************)
(* Weighted union-find                                                        *)
(******************************************************************************)

Module WUF.

Definition R := [eqType of nat].
Definition Ridx := 0.
Definition Rop := addn_comoid.
Definition cmp := leq.

Definition mfind n := mfind Ridx (T := [finType of 'I_n]).
Definition munion n := munion Rop cmp (T := [finType of 'I_n]).

End WUF.

Require Import extraction_ocaml.

Extraction Inline
  mfind_rec mfind munion WUF.R WUF.Ridx WUF.Rop WUF.cmp
  Monoid.operator Monoid.com_operator addn_comoid addn_monoid.

Set Extraction Flag 2031.
Extract Type Arity AState 0.

Extraction "../../ocaml/wuf_o0.ml" WUF.

Set Extraction Flag 8175.
Extract Type Arity AState 1.

Extraction "../../ocaml/wuf.ml" WUF.
