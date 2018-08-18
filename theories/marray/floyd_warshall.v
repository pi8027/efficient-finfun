Require Import all_ssreflect core.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Floyd_Warshall_Reachability.
Section Floyd_Warshall_Reachability.

Variable (T : finType).

Definition G := {ffun T * T -> bool}.

Definition floyd_warshall_zero (g : G) : G :=
  [ffun xy => (xy.1 == xy.2) || g xy].

Definition floyd_warshall_succ (g : G) (y : T) : G :=
  [ffun xz => let '(x, z) := xz in (g (x, y) && g (y, z)) || g (x, z)].

Definition connect (g : G) (P : pred T) (x y : T) :=
  [|| g (x, y), (x == y) |
    [exists y', connect (fun a b => P b && g (a, b)) x y' && g (y', y)]].

Lemma invariant_zero (g : G) :
  prod_uncurry (floyd_warshall_zero g) =2 connect g pred0.
Proof.
move => x y; rewrite /prod_uncurry /floyd_warshall_zero /connect !ffunE /= orbC.
case_eq (g (x, y)); case: (altP (x =P y)) => //= Hxy1 /negbT Hxy2.
by apply/esym/existsP; case => y' /andP [] /connectP [] [] //= _ ->; apply/negP.
Qed.

Lemma invariant_succ (g : G) P y :
  prod_uncurry g =2 connect g P ->
  prod_uncurry (floyd_warshall_succ g y) =2 connect g (predU1 y P).
Proof.
rewrite /prod_uncurry => /= H x z.
rewrite /floyd_warshall_succ /connect ffunE orbC.
case_eq (g (x, z)) => //= /negbT.
rewrite H /connect !negb_or negb_exists => /and3P [] H0 H1 _.
rewrite (negbTE H1) /=; apply/idP/existsP;
  [ case/andP; rewrite !H /connect => /or3P [] H2 /or3P [] H3 //= |
    case => z' /andP [] /connectP [xs Hxs ->] H2].
- by exists y; rewrite H3 andbT;
     apply/connectP; exists [:: y] => //=; rewrite eqxx H2.
- by move/eqP: H3 H2 H0 => -> ->.
- by case/existsP: H3 => z' /andP [H3 H4]; exists z'; rewrite H4 andbT;
     case/connectP: H3 => ys H3 Hz'; subst z'; apply/connectP; exists (y :: ys);
     rewrite //= eqxx H2 /=; apply/sub_path: H3 => a b /andP [] -> ->;
     rewrite orbT.
- by move/eqP: H2 H3 H0 => -> ->.
- by move/eqP: H2 H3 H1 => -> ->.
- by move/eqP: H2 H3 => <- {y} /existsP [] z' /andP [H2 H3]; exists z';
     rewrite H3 andbT; apply/connect_sub: H2 => a b /andP [] H4 H5;
     apply/connect1; rewrite H4 H5 orbT.
- by exists y; rewrite {}H3 andbT;
     case/existsP: H2 => y' /andP [] /connectP [xs H2 Hy'] H3; subst y';
     apply/connectP; exists (rcons xs y);
     rewrite (rcons_path, last_rcons) //= eqxx H3 /= andbT;
     apply/sub_path: H2 => a b /andP [] -> ->; rewrite orbT.
- by move/eqP: H3 H2 => -> {y} /existsP [z'] /andP [] H2 H3; exists z';
     rewrite H3 andbT; apply/connect_sub: H2 => a b /andP [H4 H5];
     apply/connect1; rewrite H4 H5 orbT.
- by move: H2 H3 => /existsP [y'] /andP [] /connectP [xs] H2 -> {y'} H3
                    /existsP [z'] /andP [] /connectP [ys] H4 -> {z'} H5;
     exists (last y ys); rewrite H5 andbT; apply/connectP;
     exists (xs ++ y :: ys); rewrite (cat_path, last_cat) //= eqxx H3 /=;
     apply/andP; split; [move: H2 | move: H4];
     apply sub_path => a b /andP [] -> ->; rewrite orbT.
(* shorten and splitting *)
-
Abort.

End Floyd_Warshall_Reachability.
End Floyd_Warshall_Reachability.

Module Floyd_Warshall.
Section Floyd_Warshall.

Variable (T : finType).

Definition G := {ffun T * T -> option nat}.

Definition add_distance (n m : option nat) : option nat :=
  match n, m with Some n', Some m' => Some (n' + m') | _, _ => None end.

Lemma add_distance_dN d : add_distance d None = None. Proof. by case: d. Qed.

Lemma add_distanceC : commutative add_distance.
Proof. by case => [? |] [? |] //=; rewrite addnC. Qed.

Lemma add_distanceA : associative add_distance.
Proof. by case => [? |] [? |] [? |] //=; rewrite addnA. Qed.

Definition lt_distance (n m : option nat) : bool :=
  match n, m with
    | None, _ => false
    | Some _, None => true
    | Some n', Some m' => n' < m'
  end.

Definition le_distance (n m : option nat) : bool := ~~ lt_distance m n.

Lemma lt_distance_d0 d : lt_distance d (Some 0) = false.
Proof. by case: d. Qed.

Lemma lt_distance_neq d1 d2 : lt_distance d1 d2 -> d1 != d2.
Proof.
by case: d1 d2 => [x |] [y |] => //= H;
   apply/eqP => -[H0]; move: H; rewrite H0 ltnn.
Qed.

Lemma lt_add_distanceL d1 d2 d3 :
  lt_distance (add_distance d1 d2) d3 -> lt_distance d1 d3.
Proof.
by case: d1 d2 d3 => [? |] [? |] [? |] => //=;
   apply leq_trans; rewrite ltnS leq_addr.
Qed.

Lemma lt_add_distanceR d1 d2 d3 :
  lt_distance (add_distance d1 d2) d3 -> lt_distance d2 d3.
Proof. by rewrite add_distanceC; apply lt_add_distanceL. Qed.

(*
Definition step (g : G) (x y : T) := if g (x, y) is Some _ then true else false.
*)

Definition floyd_warshall_zero (g : G) : G :=
  [ffun xy => let '(x, y) := xy in if x == y then Some 0 else g xy].

Definition floyd_warshall_succ (g : G) (y : T) : G :=
  [ffun xz =>
   let '(x, z) := xz in
   let xyz := add_distance (g (x, y)) (g (y, z)) in
   if lt_distance xyz (g (x, z)) then xyz else g (x, z)].

Definition m_floyd_warshall : AState {ffun T * T -> option nat} unit :=
  let iterate := @miterate_revfin T unit _ in
  iterate (fun i _ => astate_set (i, i) (Some 0)) tt;;
  iterate (fun i _ =>
    iterate (fun j _ =>
      d_ji <- astate_get (j, i);
      if d_ji isn't Some dji then astate_ret tt else
      iterate (fun k _ =>
        d_ik <- astate_get (i, k);
        if d_ik isn't Some dik then astate_ret tt else
        d_jk <- astate_get (j, k);
        if d_jk isn't Some djk then astate_set (j, k) (Some (dji + dik))
        else if djk <= dji + dik
             then astate_ret tt
             else astate_set (j, k) (Some (dji + dik))
      ) tt
    ) tt
  ) tt.

End Floyd_Warshall.

Definition floyd_warshall
           (n : nat) (g : {ffun 'I_n * 'I_n -> option nat}) :
  {ffun 'I_n * 'I_n -> option nat} :=
  iterate_revfin
    (fun i => @floyd_warshall_succ [finType of 'I_n] ^~ i)
    (floyd_warshall_zero g).

Definition floyd_warshall_fast
           (n : nat) (g : {ffun 'I_n * 'I_n -> option nat}) :
  {ffun 'I_n * 'I_n -> option nat} :=
  snd (run_AState (m_floyd_warshall _) g).

End Floyd_Warshall.

Require Import extraction_ocaml.
Unset Extraction SafeImplicits.
Set Extraction Flag 8175.

Extraction Inline
  Floyd_Warshall.add_distance Floyd_Warshall.lt_distance
  Floyd_Warshall.floyd_warshall_zero Floyd_Warshall.floyd_warshall_succ
  Floyd_Warshall.m_floyd_warshall.

Extraction "../../ocaml/floyd_warshall.ml" Floyd_Warshall.
