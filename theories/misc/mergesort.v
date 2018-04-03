Require Import all_ssreflect all_algebra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition perm_eq' := @perm_eq.

Section Perm.

Variable (A : eqType) (le : A -> A -> bool).

Definition condrev (r : bool) (xs : seq A) :=
  if r then rev xs else xs.

Lemma perm_catrev (xs ys : seq A) : perm_eq (catrev xs ys) (xs ++ ys).
Proof.
by elim: xs ys => //= x xs IH ys; apply (perm_eq_trans (IH _));
  rewrite -cat_rcons -cat_cons perm_cat2r perm_rcons.
Qed.

Lemma perm_rev (xs : seq A) : perm_eq (rev xs) xs.
Proof. by rewrite -{2}(cats0 xs) perm_catrev. Qed.

Lemma perm_condrev (r : bool) (xs : seq A) : perm_eq (condrev r xs) xs.
Proof. by case: r => //=; apply perm_rev. Qed.

Lemma count_flatten (xss : seq (seq A)) x:
  count x (flatten xss) = \sum_(xs <- xss) (count x xs).
Proof.
elim: xss => //= [| xs xss IH]; first by rewrite big_nil.
by rewrite count_cat big_cons IH.
Qed.

Lemma perm_flatten (xs ys : seq (seq A)) :
  perm_eq xs ys -> perm_eq (flatten xs) (flatten ys).
Proof.
by move => H; apply/perm_eqP => x; rewrite !count_flatten; apply eq_big_perm.
Qed.

Fixpoint perm_common (xs : seq A) : seq A -> seq A :=
  if xs isn't x :: xs
  then fun _ => [::]
  else fix perm_common' (ys : seq A) :=
    if ys isn't y :: ys
    then [::]
    else if x == y
         then x :: perm_common xs ys
         else if le x y
              then perm_common xs (y :: ys)
              else perm_common' ys.

Fixpoint perm_elim (xs : seq A) : seq A -> seq A * seq A :=
  if xs isn't x :: xs
  then fun ys => ([::], ys)
  else fix perm_elim' (ys : seq A) :=
    if ys isn't y :: ys
    then (x :: xs, [::])
    else if x == y
         then perm_elim xs ys
         else if le x y
              then let (xs', ys') := perm_elim xs (y :: ys) in
                   (x :: xs', ys')
              else let (xs', ys') := perm_elim' ys in (xs', y :: ys').

Lemma perm_elim_perm (xs ys : seq A) :
  let (xs', ys') := perm_elim xs ys in
  perm_eq xs (perm_common xs ys ++ xs') /\
  perm_eq ys (perm_common xs ys ++ ys').
Proof.
elim: xs ys => //= x xs IHx; elim => // y ys IHy.
case: eqP => [-> | _]; first by
  case: {IHx IHy} (perm_elim xs ys) (IHx ys) => /= xs' ys'; rewrite !perm_cons.
case: ifP => _; first by
  case: (perm_elim xs (y :: ys)) (IHx (y :: ys)) => /= xs' ys' [H ->];
    split => //; move/perm_eqlP/perm_eqrP:
      (perm_catC (perm_common xs (y :: ys)) (x :: xs')) => -> /=;
    rewrite perm_cons; move/perm_eqlP: H => ->; apply/perm_eqlP/perm_catC.
case: (_ ys) {IHx} IHy => xs' ys' [->].
set c := (fix perm_common' (ys : seq A) : seq A := _).
move => H; split => //.
move/perm_eqlP/perm_eqrP: (perm_catC (c ys) (y :: ys')) => -> /=.
by rewrite perm_cons; move/perm_eqlP: H => ->; apply/perm_eqlP/perm_catC.
Qed.

End Perm.

Section PermSyntax.

Variable (A : Type).

Inductive Seq : Type :=
  | SeqEmbed  of seq A
  | SeqNil
  | SeqCons   of A & Seq
  | SeqRcons  of Seq & A
  | SeqCat    of Seq & Seq
  | SeqCatrev of Seq & Seq
  | SeqRev    of Seq.

Fixpoint denote_Seq (xs : Seq) : seq A :=
  match xs with
    | SeqEmbed xs => xs
    | SeqNil => [::]
    | SeqCons x xs => x :: denote_Seq xs
    | SeqRcons xs x => rcons (denote_Seq xs) x
    | SeqCat xs ys => denote_Seq xs ++ denote_Seq ys
    | SeqCatrev xs ys => catrev (denote_Seq xs) (denote_Seq ys)
    | SeqRev xs => rev (denote_Seq xs)
  end.

Fixpoint norm_Seq (r : bool) (xs : Seq) (acc : seq (bool * seq A)) :
  seq (bool * seq A) :=
  match xs with
    | SeqEmbed xs => (r, xs) :: acc
    | SeqNil => acc
    | SeqCons x xs =>
      if r
        then norm_Seq true xs ((false, [:: x]) :: acc)
        else (false, [:: x]) :: norm_Seq false xs acc
    | SeqRcons xs x =>
      if r
        then (false, [:: x]) :: norm_Seq true xs acc
        else norm_Seq false xs ((false, [:: x]) :: acc)
    | SeqCat xs ys =>
      if r
        then norm_Seq true ys (norm_Seq true xs acc)
        else norm_Seq false xs (norm_Seq false ys acc)
    | SeqCatrev xs ys =>
      if r
        then norm_Seq true ys (norm_Seq false xs acc)
        else norm_Seq true xs (norm_Seq false ys acc)
    | SeqRev xs => norm_Seq (~~ r) xs acc
  end.

End PermSyntax.

Section PermReflection.

Variable (A : eqType).

Lemma norm_SeqE (r : bool) (xs : Seq A) (acc : seq (bool * seq A)) :
  flatten [seq condrev e.1 e.2 | e <- norm_Seq r xs acc] =
  condrev r (denote_Seq xs) ++ flatten [seq condrev e.1 e.2 | e <- acc].
Proof.
by elim: xs r acc =>
  [xs || x xs IH | xs IH x | xs IHl ys IHr | xs IHl ys IHr | xs IH] [] acc //=;
  (rewrite IH || rewrite ?(IHl, IHr));
  rewrite ?(catrevE, rev_cons, rev_rcons, rev_cat, revK, cat_rcons, catA) //=.
Qed.

Lemma norm_Seq_perm (xs : Seq A) :
  perm_eq (denote_Seq xs) (flatten (map snd (norm_Seq false xs [::]))).
Proof.
rewrite -(cats0 (denote_Seq xs)) -/(condrev false (denote_Seq xs))
        (_ : [::] = flatten [seq condrev e.1 e.2 | e <- [::]]) // -norm_SeqE.
by elim: (norm_Seq _ _ _) => //= {xs} -[r xs] ys /=; rewrite -(perm_cat2l xs);
  apply perm_eq_trans; rewrite perm_cat2r perm_condrev.
Qed.

Lemma perm_Seq_flatten (xs ys : Seq A) :
  perm_eq' (denote_Seq xs) (denote_Seq ys) =
  perm_eq' (flatten (map snd (norm_Seq false xs [::])))
           (flatten (map snd (norm_Seq false ys [::]))).
Proof.
rewrite /perm_eq'; apply/idP; case: ifP;
  last (move/negP => H H0; apply/H => {H}; move: H0); move => H.
- by rewrite (perm_eqlP (norm_Seq_perm _))
             (perm_eqlP H) perm_eq_sym norm_Seq_perm.
- by rewrite -(perm_eqrP (norm_Seq_perm ys))
             -(perm_eqrP H) perm_eq_sym norm_Seq_perm.
Qed.

Lemma perm_fm_sort_elim (f : nat -> seq A) (xs ys : seq nat) :
  perm_eq' (flatten (map f xs)) (flatten (map f ys)) =
  let (xs', ys') := perm_elim geq (sort geq xs) (sort geq ys) in
  perm_eq' (flatten (map f xs')) (flatten (map f ys')).
Proof.
rewrite /perm_eq'.
case: (perm_elim _ _ _) (perm_elim_perm geq (sort geq xs) (sort geq ys))
  => xs' ys' [].
rewrite !perm_sort => /(perm_map f) /perm_flatten /perm_eqlP ->
                       /(perm_map f) /perm_flatten /perm_eqrP ->.
by rewrite !map_cat !flatten_cat perm_cat2l.
Qed.

End PermReflection.

Ltac seqReify xs :=
  match xs with
    | @nil ?A => constr:(SeqNil A)
    | ?x :: ?xs => let xs' := seqReify xs in constr:(SeqCons x xs')
    | rcons ?xs ?x => let xs' := seqReify xs in constr:(SeqRcons xs' x)
    | ?xs ++ ?ys =>
      let xs' := seqReify xs in
      let ys' := seqReify ys in
      constr:(SeqCat xs' ys')
    | catrev ?xs ?ys =>
      let xs' := seqReify xs in
      let ys' := seqReify ys in
      constr:(SeqCatrev xs' ys')
    | rev ?xs => let xs' := seqReify xs in constr:(SeqRev xs')
    | _ => constr:(SeqEmbed xs)
  end.

Ltac autoperm :=
  let X := fresh "X" in
  let rec num_rec Heq f xss :=
    match xss with
      | [::] => idtac
      | ?xs :: ?xss =>
        let f' := fresh "f" in
        rename f into f';
        pose f := (fun n : nat => if n is n'.+1 then f' n' else xs);
        rewrite [in X in X = _](_ : xs = f 0) //
                ?[in X in X = _](_ : forall n : nat, f' n = f n.+1) // in Heq;
        subst f'; num_rec Heq f xss
      | _ :: ?xss => num_rec Heq f xss
    end
  in
  let autoperm_sub Heq f A xs ys :=
    let xs' := seqReify xs in
    let ys' := seqReify ys in
    have Heq := erefl (@perm_eq A xs ys);
    pose f := (fun n : nat => [::] : seq A);
    rewrite -{1}/perm_eq'
            (_ : perm_eq' xs ys = perm_eq' (denote_Seq xs') (denote_Seq ys')) //
            perm_Seq_flatten ![map snd (norm_Seq false _ [::])]/= in Heq;
    match goal with [Heq : perm_eq' (flatten ?xs') (flatten ?ys') = _ |- _] =>
      num_rec Heq f xs'; num_rec Heq f ys'
    end;
    rewrite -/(map f [::]) -?(map_cons f) perm_fm_sort_elim in Heq;
    let pe := fresh "pe" in set pe := perm_elim _ _ _ in Heq;
    native_compute in pe; subst pe; rewrite [X in X = _]/= ?[in X in X = _]cats0 in Heq
  in
  repeat
  (let Heq := fresh "H" in
   let f := fresh "f" in
   match goal with
     | [|- context [@perm_eq ?A ?xs ?ys]] =>
       autoperm_sub Heq f A xs ys; rewrite -{}Heq {f}
     | [H : context [@perm_eq ?A ?xs ?ys] |- _] =>
       autoperm_sub Heq f A xs ys; rewrite -{}Heq {f} in H
   end);
  unfold perm_eq' in *; try by [].

Module PermExamples.

Example ex1 (A : eqType) (x y z : A) (xs ys zs zs' : seq A) :
  perm_eq (xs ++ zs) (zs' ++ xs) ->
  perm_eq (x :: xs ++ y :: ys ++ z :: zs)
          (rev zs' ++ [:: x; y] ++ ys ++ z :: rev xs).
Proof.
Time autoperm.
Qed.

Example ex2 (A : eqType) (xs ys zs xs' ys' zs' : seq A) :
  perm_eq xs xs' -> perm_eq ys ys' -> perm_eq zs zs' ->
  perm_eq (catrev xs ys ++ zs) (xs' ++ rev ys' ++ zs').
Proof.
Time autoperm. (* preserves the order of terms. *)
rewrite -(perm_cat2r (ys ++ zs)) => /perm_eqlP ->.
rewrite perm_cat2l -(perm_cat2r zs) => /perm_eqlP ->.
by rewrite perm_cat2l.
Qed.

Example ex3 (A B : eqType) (f : A -> B) (xs ys xs' : seq A) (zs : seq B) :
  perm_eq (xs ++ xs) (xs' ++ xs) ->
  perm_eq (map f (xs ++ ys) ++ zs) (map f ys ++ zs ++ map f xs').
Proof.
rewrite map_cat.
Time autoperm.
apply perm_map.
Qed.

End PermExamples.

(* Mergesort *)

Lemma total_asym (T : Type) (R : rel T) :
  total R -> forall x y : T, ~~ R x y -> R y x.
Proof. by move => H x y /negPf H0; move: (H x y); rewrite H0. Qed.

Module Mergesort.
Section Mergesort.

Variables (A : eqType) (cmp : A -> A -> bool).

Fixpoint merge xs :=
  match xs with
    | [::] => id
    | x :: xs' =>
      fix merge' ys {struct ys} :=
        if ys is y :: ys'
          then if cmp x y then x :: merge xs' ys else y :: merge' ys'
          else xs
  end.

Fixpoint merge_pair xs :=
  match xs with
    | [::] => [::]
    | [:: x] => [:: x]
    | (x :: x' :: xs) => merge x x' :: merge_pair xs
  end.

Fixpoint list2_rec (A : Type) (P : seq A -> Set)
  (c1 : P [::]) (c2 : forall x, P [:: x])
  (c3 : forall x x' xs, P xs -> P [:: x, x' & xs]) (xs : seq A) : P xs :=
  match xs with
    | [::] => c1
    | [:: x] => c2 x
    | [:: x, x' & xs] => c3 x x' xs (list2_rec c1 c2 c3 xs)
  end.

Lemma merge_pair_leq xs : size (merge_pair xs) <= (size xs).
Proof. by elim/list2_rec: xs => //= _ _ xs /leqW; rewrite ltnS. Qed.

Lemma Acc_ltsize T : well_founded (fun (x y : seq T) => size x < size y).
Proof.
move => xs.
elim: {xs} (size xs) {1 3}xs (leqnn (size xs)) => [[] // |] n IH xs H.
constructor => ys /(fun H0 => leq_trans H0 H) {H}; rewrite ltnS.
apply IH.
Qed.

Definition sort (xs : seq A) : seq A :=
  Fix (@Acc_ltsize (seq A)) (fun _ => seq A)
    (fun xss : seq (seq A) =>
      match xss return (forall yss, size yss < size xss -> seq A) -> seq A with
        | [::] => fun _ => [::]
        | [:: xs] => fun _ => xs
        | (xs :: xs' :: xss') as xss =>
          fun (H : forall yss, size yss <= (size xss').+1 -> seq A) =>
            H (merge_pair xss) (merge_pair_leq xss')
      end)
  (map (fun x => [:: x]) xs).

Lemma sort_sorted (xs : seq A) : total cmp -> sorted cmp (sort xs).
Proof.
rewrite /sort /Fix => Hcmp.
set xss := map _ _.
have H: all (sorted cmp) xss by rewrite {}/xss; elim: xs.
move: (Acc_ltsize _) => Hi.
elim/Acc_ind: xss / Hi (Hi) H => {xs} -[| xs [| xs' xss]] _ IH Hi;
  rewrite -Fix_F_eq //; first by rewrite /= andbT.
move => H; apply IH; first by rewrite !ltnS merge_pair_leq.
elim/list2_rec: {xs xs' xss H Hi IH} [:: _, _ & _] H =>
  //= xs xs' xss IH /and3P [H H0 H1]; rewrite {}IH // andbT.
by elim: xs xs' H H0 {xss H1} => // x xs IHx;
  elim => // y ys IHy /= H H0; case: ifPn => [| /(total_asym Hcmp)] H1;
  [ case: xs {IHx IHy} H (IHx (y :: ys) (path_sorted H) H0) => /= [| x' xs] |
    case: ys {IHy} H0 (IHy H (path_sorted H0)) => /= [| y' ys] ];
  rewrite ?H1 //; case: ifPn => [| /(total_asym Hcmp)] H2 /= /andP [H3 _];
  rewrite ?H1 ?H3.
Qed.

Lemma perm_sort (xs : seq A) : perm_eq xs (sort xs).
Proof.
rewrite /sort /Fix.
set xss := map _ _.
have {1}->: xs = flatten xss by rewrite {}/xss; elim: xs => //= x xs {1}->.
move: (Acc_ltsize _) => Hi.
elim/Acc_ind: xss / Hi (Hi) => {xs} -[| xs [| xs' xss]] _ IH Hi;
  rewrite -Fix_F_eq //; first by rewrite /= cats0.
apply perm_eq_trans with (flatten (merge_pair (xs :: xs' :: xss)));
  last by apply IH; rewrite /= !ltnS merge_pair_leq.
elim/list2_rec: {xs xs' xss IH Hi} [:: _, _ & _] => //= xs xs' xss.
rewrite -(perm_cat2l (merge xs xs')) => /perm_eqrP <-; autoperm.
by elim: xs xs' {xss} => // x xs IHx;
  elim => [| y ys IHy /=]; last case: ifP; autoperm.
Qed.

Definition sort_finfun (I : finType) (a : {ffun I -> A}) : {ffun I -> A} :=
  let '(Tuple xs Hxs) := fgraph a in
  Finfun
    (@Tuple #|I| A (sort xs)
                   (eq_ind _ (eq_op ^~ #|I|) Hxs _
                           (perm_eq_size (perm_sort xs)))).

End Mergesort.
End Mergesort.

(* Tail-recursive Mergesort *)

Lemma flatten_filter (T : eqType) (xss : seq (seq T)) :
  flatten (filter (fun xs => xs != [::]) xss) = flatten xss.
Proof. by elim: xss => // -[| x xs] xss //= ->. Qed.

Lemma sorted_cat (A : eqType) (cmp : A -> A -> bool) (xs ys : seq A) :
  sorted cmp (xs ++ ys) =
  (sorted cmp xs && sorted cmp ys &&
   match ohead (rev xs), ohead ys with
     | Some x, Some y => cmp x y
     | _, _ => true
   end).
Proof.
rewrite -(revK xs); move: {xs} (rev xs) => xs; rewrite revK.
case: xs => [| x xs]; first by rewrite andbT.
case: ys => [| y ys]; first by rewrite /= cats0 !andbT.
rewrite rev_cons -cats1 -catA /=.
case: {xs} (rev xs) => [| x' xs]; first by rewrite andbC.
by rewrite /= !cat_path /= andbT (andbC (cmp x y)) !andbA.
Qed.

Module Mergesort_tailrec.

Lemma catrevE' (T : Type) (s t : seq T) : catrev s t = rev (rev t ++ s).
Proof. by rewrite catrevE rev_cat revK. Qed.

Definition cmplex (A : Type) (cmp1 cmp2 : rel A) (x y : A) : bool :=
  cmp1 x y && (~~ cmp1 y x || cmp2 x y).

Section Merge.

Variables (A : eqType) (cmp1 cmp2 : A -> A -> bool).
Hypothesis (Hcmp1 : total cmp1).

Notation cmplex := (cmplex cmp1 cmp2).

Fixpoint merge (xs : seq A) : seq A -> seq A -> seq A :=
  if xs is x :: xs'
  then fix merge' (ys acc : seq A) :=
         if ys is y :: ys'
         then if cmp1 x y
              then merge xs' ys (x :: acc)
              else merge' ys' (y :: acc)
         else catrev xs acc
  else @catrev _.

Lemma merge_perm (xs ys acc : seq A) :
  perm_eq (merge xs ys acc) (xs ++ ys ++ acc).
Proof.
elim: xs ys acc => [ys acc /= | x xs IHx]; last elim => [| y ys IHy] acc /=;
  last (case: ifP => _; rewrite ?(perm_eqlP (IHx _ _)) ?(perm_eqlP (IHy _)));
  autoperm.
Qed.

Lemma merge_sorted_rec (xs ys acc : seq A) :
  sorted cmplex xs -> sorted cmplex ys -> sorted (fun x y => cmplex y x) acc ->
  (forall x y : A, x \in xs -> y \in ys -> cmp2 x y) ->
  match acc with
  | [::] => true
  | a :: _ => (if xs is x :: _ then cmplex a x else true) &&
              (if ys is y :: _ then cmplex a y else true)
  end ->
  sorted (fun x y => cmplex y x) (merge xs ys acc).
Proof.
elim: xs ys acc => /= [| x xs IHx]; elim => /= [| y ys IHy]; try by
  case => [| a acc] //= Hx Hy Ha H; rewrite ?andbT => H0;
  rewrite catrevE' rev_sorted //= rev_cons cat_rcons
          sorted_cat revK rev_sorted /= ?Hx ?Hy ?Ha ?H0.
move => acc Hx Hy Ha H H0; case: ifPn => H1; [apply IHx | apply IHy] => //=.
- apply (path_sorted Hx).
- by case: acc Ha H0 => //= a acc -> /andP [] ->.
- by move => x' y' H2; rewrite inE => /orP [/eqP |] H3;
    apply H; rewrite inE ?H2 ?H3 ?eqxx ?orbT.
- by case: xs Hx H {IHx IHy} => [| x' xs] /=;
    [move => _ | case/andP => -> _] => /(_ x y);
    rewrite /cmplex H1 !inE !eqxx => -> //; rewrite orbT.
- apply (path_sorted Hy).
- by case: acc Ha H0 => //= a acc -> /andP [] _ ->.
- by move => x' y'; rewrite inE => /orP [/eqP |] H2 H3;
    apply H; rewrite inE ?H2 ?H3 ?eqxx ?orbT.
- by rewrite {1}/cmplex H1 (total_asym Hcmp1 H1) /=;
    case: ys Hy {H IHx IHy} => [| y' ys] //= /andP [] ->.
Qed.

Lemma merge_sorted (xs ys : seq A) :
  sorted cmplex xs -> sorted cmplex ys ->
  (forall x y : A, x \in xs -> y \in ys -> cmp2 x y) ->
  sorted (fun x y => cmplex y x) (merge xs ys [::]).
Proof. by move => *; apply merge_sorted_rec. Qed.

End Merge.

Section Mergesort.

Variables (A : eqType) (cmp1 cmp2 : A -> A -> bool).
Hypothesis (Hcmp1 : total cmp1) (Hcmp2 : transitive cmp2).

Notation cmplex := (cmplex cmp1 cmp2).

Fixpoint merge_sort_push
         (r : bool) (xs : seq A) (yss : seq (seq A)) : seq (seq A) :=
  match yss with
    | [::] :: yss' | [::] as yss' => xs :: yss'
    | ys :: yss =>
      let zs :=
          if r
          then merge (fun x y => cmp1 y x) xs ys [::]
          else merge cmp1 ys xs [::]
      in
      [::] :: merge_sort_push (~~ r) zs yss
  end.

Lemma merge_sort_push_perm (r : bool) (xs : seq A) (yss : seq (seq A)) :
  perm_eq (flatten (merge_sort_push r xs yss)) (xs ++ flatten yss).
Proof.
elim: yss r xs => [| [| y ys] yss IH] r xs //=;
  rewrite (perm_eqlP (IH _ _)); autoperm; case: r;
  rewrite -/(merge _ (_ :: _) _) (perm_eqlP (merge_perm _ _ _ [::])); autoperm.
Qed.

Lemma merge_sort_push_sorted (r : bool) (xs : seq A) (yss : seq (seq A)) :
  sorted (if r then fun x y => cmplex y x else cmplex) xs ->
  path (fun xs ys => all (fun x => all (fun y => cmp2 y x) ys) xs) xs
    (filter (fun ys => ys != [::]) yss) ->
  foldr (fun ys f r =>
           sorted (if r then fun x y => cmplex y x else cmplex) ys && f (~~ r))
        xpredT yss r ->
  let yss' := merge_sort_push r xs yss in
  sorted (fun xs ys => all (fun x => all (fun y => cmp2 y x) ys) xs)
    (filter (fun ys => ys != [::]) yss') &&
  foldr (fun ys f r =>
           sorted (if r then fun x y => cmplex y x else cmplex) ys &&
           f (~~ r))
        xpredT yss' r.
Proof.
elim: yss r xs => [/= r xs -> |]; first case: ifP => //.
case; first by
  move => /= yss IH r xs ->; case: ifP => /= [_ | _ /path_sorted] -> ->.
move => y ys yss IH r xs H /= /andP [H0 H1] /andP [H2 H3].
rewrite -/(merge _ (_ :: _) _ _).
set xs' := if r then _ else _.
suff/andP [H4 H5]:
  sorted (if r then cmplex else fun x y => cmplex y x) xs' &&
  path (fun xs ys => all (fun x : A => all (cmp2^~ x) ys) xs) xs'
       (filter (fun ys => ys != [::]) yss) by
  move: (IH (~~ r) xs'); rewrite if_neg H3 => /(_ H4 H5 erefl) /= ->.
subst xs'; case: r H H2 {H3} => H H2;
  rewrite merge_sorted 1?(lock merge) //= -?lock.
- case: {yss IH} (filter _ yss) H1 => //= ys' yss /andP [H1 ->];
    rewrite andbT; apply/allP => x';
    rewrite (perm_eq_mem (merge_perm _ _ _ _)) cats0 mem_cat => /orP [];
    last by move: x'; apply/allP => //=.
  by case/andP: H1 => H1 _; case/(allP H0)/andP => H3 _;
    apply/allP => y' /(allP H1) H4; apply (Hcmp2 H4 H3).
- by move => x' y' /(allP H0) /andP [H3 H4];
    rewrite inE => /orP [/eqP -> | /(allP H4)].
- case: {yss IH} (filter _ yss) H1; rewrite (lock all) (lock merge)
    => //= ys' yss /andP []; rewrite -!lock => H1 ->; rewrite andbT.
  apply/allP => x'; rewrite (perm_eq_mem (merge_perm _ _ _ _)) cats0 mem_cat
    => /orP [/(allP H1) |] // /(allP H0) /andP [H3 _].
  by case/andP: H1 => H4 _;
    apply/allP => y' /(allP H4) H5; apply (Hcmp2 H5 H3).
- by move => y' x'; rewrite inE =>
    /orP [/eqP -> | H3] /(allP H0) /andP [H4] // /allP /(_ _ H3).
Qed.

Fixpoint merge_sort_pop (r : bool) (xs : seq A) (yss : seq (seq A)) : seq A :=
  match yss with
    | [::] => if r then rev xs else xs
    | [::] :: [::] :: yss => merge_sort_pop r xs yss
    | [::] :: yss => merge_sort_pop (~~ r) (rev xs) yss
    | ys :: yss =>
      let zs :=
          if r
          then merge (fun x y => cmp1 y x) xs ys [::]
          else merge cmp1 ys xs [::]
      in
      merge_sort_pop (~~ r) zs yss
  end.

Lemma merge_sort_pop_perm (r : bool) (xs : seq A) (yss : seq (seq A)) :
  perm_eq (merge_sort_pop r xs yss) (xs ++ flatten yss).
Proof.
move: yss r xs; fix IH 1 => -[| [[| [| y ys] yss] | y ys yss]] r xs //=;
  (try by case: r => /=; autoperm);
  rewrite ?negbK ?if_neg (perm_eqlP (IH _ _ _)); autoperm;
  case: r; rewrite -/(merge _ (_ :: _) _) (perm_eqlP (merge_perm _ _ _ _));
  autoperm.
Qed.

Lemma merge_sort_pop_sorted (r : bool) (xs : seq A) (yss : seq (seq A)) :
  sorted (if r then fun x y => cmplex y x else cmplex) xs ->
  path (fun xs ys => all (fun x => all (fun y => cmp2 y x) ys) xs) xs
    (filter (fun ys => ys != [::]) yss) ->
  foldr (fun ys f r =>
           sorted (if r then fun x y => cmplex y x else cmplex) ys && f (~~ r))
        xpredT yss r ->
  sorted cmplex (merge_sort_pop r xs yss).
Proof.
move: yss r xs; fix IH 1 => -[| [[| [| y ys] yss] | y ys yss]] r xs //=.
- by case: r; rewrite //= rev_sorted.
- by rewrite revK; case: r => //=; rewrite rev_sorted.
- by rewrite negbK; apply IH.
- rewrite negbK => H /andP [H0 H1] /andP [H2 H3].
  rewrite -/(merge _ (_ :: _) _ _) (lock merge); apply IH => //.
  + case: r H H2 {H3} => /=; rewrite -lock => H H2; apply merge_sorted;
      rewrite ?rev_sorted // => x' y'; rewrite mem_rev inE.
    * by case/orP => [/eqP -> | H3] /(allP H0) /andP [] // _ /allP /(_ _ H3).
    * by case/(allP H0)/andP => H3 H4 /orP [/eqP -> | /(allP H4)].
  + case: {yss H3} (filter _ yss) H1 =>
      // ys' yss /= /andP [] /andP [] H1 H3 ->; rewrite andbT; apply/allP => x.
    rewrite
      -lock (fun_if (fun xs => x \in xs)) !(perm_eq_mem (merge_perm _ _ _ _))
      !cats0 (perm_eq_mem (introT perm_eqlP (perm_catC _ _)))
      if_same mem_cat mem_rev inE -orbA.
    by move => /or3P [/eqP -> | /(allP H3) |] // /(allP H0) /andP [H4 _];
      apply/allP => y' /(allP H1) H5; apply (Hcmp2 H5 H4).
- move => H /andP [H0 H1] /andP [H2 H3].
  rewrite -/(merge _ (_ :: _) _ _) (lock merge); apply IH => //.
  + case: r H H2 {H3} => /=; rewrite -lock => H H2;
      apply merge_sorted => // x' y'; rewrite inE.
    * by case/(allP H0)/andP => H3 H4 /orP [/eqP -> | /(allP H4)].
    * by case/orP => [/eqP -> | H3] /(allP H0) /andP [] // _ /allP /(_ _ H3).
  + case: {yss H3} (filter _ yss) H1 =>
      // ys' yss /= /andP [] /andP [] H1 H3 ->; rewrite andbT; apply/allP => x.
    rewrite
      -lock (fun_if (fun xs => x \in xs)) !(perm_eq_mem (merge_perm _ _ _ _))
      !cats0 (perm_eq_mem (introT perm_eqlP (perm_catC _ _)))
      if_same mem_cat inE -orbA.
    by move => /or3P [/eqP -> | /(allP H3) |] // /(allP H0) /andP [H4 _];
      apply/allP => y' /(allP H1) H5; apply (Hcmp2 H5 H4).
Qed.

Fixpoint merge_sort_rec (xss : seq (seq A)) (xs : seq A) : seq A :=
  match xs with
    | [::] | [:: _] => merge_sort_pop false xs xss
    | x :: x' :: xs' =>
      merge_sort_rec
        (merge_sort_push
           false (if cmp1 x x' then [:: x; x'] else [:: x'; x]) xss)
        xs'
  end.

Lemma merge_sort_rec_perm (xss : seq (seq A)) (xs : seq A) :
  perm_eq (merge_sort_rec xss xs) (xs ++ flatten xss).
Proof.
move: xs xss; fix IH 1 => -[| x [| x' xs]] xss /=;
  rewrite ?(perm_eqlP (merge_sort_pop_perm _ _ _)); autoperm;
  case: ifP => _; rewrite (perm_eqlP (IH _ _)); autoperm;
  rewrite (perm_eqlP (merge_sort_push_perm _ _ _)); autoperm.
Qed.

Lemma merge_sort_rec_sorted (xss : seq (seq A)) (xs : seq A) :
  sorted cmp2 xs ->
  path (fun xs ys => all (fun x => all (fun y => cmp2 y x) ys) xs) xs
    (filter (fun xs => xs != [::]) xss) ->
  foldr (fun xs f r =>
           sorted (if r then fun x y => cmplex y x else cmplex) xs && f (~~ r))
        xpredT xss false ->
  sorted cmplex (merge_sort_rec xss xs).
Proof.
move: xs xss; fix IH 1 => -[| x [| x' xs]] xss /=;
  try by move => *; apply merge_sort_pop_sorted.
case/andP => H H0 H1 H2.
have H3: sorted cmplex (if cmp1 x x' then [:: x; x'] else [:: x'; x])
  by case: ifPn => /= H3; rewrite /cmplex H3 ?H ?orbT ?(total_asym Hcmp1 H3).
have H4:
  path (fun xs ys => all (fun x => all (fun y => cmp2 y x) ys) xs)
    (if cmp1 x x' then [:: x; x'] else [:: x'; x]) [seq ys <- xss | ys != [::]]
  by case: {xss H2 H3} (filter _ _) H1 => //= xs' xss'; rewrite -!andbA
    => /and4P [H1 H2 H3 ->]; rewrite andbT; apply/allP => ?;
    rewrite (fun_if (fun xs => _ \in xs)) !inE orbC if_same => /orP [] /eqP ->.
move: (merge_sort_push_sorted (r := false) H3 H4 H2) => /= /andP [] H5 H6.
apply: IH => // {H2 H3 H4 H6}; first by apply (path_sorted H0).
move: H5; set xss' := filter _ _.
have: perm_eq (flatten xss') (x' :: x :: flatten xss) by
  rewrite flatten_filter (perm_eqlP (merge_sort_push_perm _ _ _));
  case: ifP; autoperm.
case: xss' => //= xs' xss' H2 ->; rewrite andbT.
apply/allP => y /(allP (order_path_min Hcmp2 H0)) H3; apply/allP => x''.
move/(@or_introl _ (x'' \in flatten xss'))/orP;
  rewrite -mem_cat (perm_eq_mem H2) !inE => /or3P [/eqP -> // | /eqP -> | H4];
  apply: (Hcmp2 _ H3) => // {xs' xss' y H H0 H2 H3}.
have H: x' \in [:: x, x' & xs] by rewrite !inE eqxx orbT.
elim: {x xs} xss x' [:: x, x' & xs] H1 H H4
    => // -[] //= x xs xss IH x' xs' /andP [H H0] /(allP H) /andP [H1 H2];
  rewrite -/(all _ (_ :: _)) -/((_ :: _) ++ _) mem_cat
    => /orP [/(allP (s := _ :: _) (introT andP (conj H1 H2))) | H3] //.
by apply: (Hcmp2 _ H1); apply (IH _ (x :: xs)) => //; rewrite inE eqxx.
Qed.

Definition sort := merge_sort_rec [::].

Lemma perm_sort (xs : seq A) : perm_eq (sort xs) xs.
Proof. by rewrite /sort (perm_eqlP (merge_sort_rec_perm _ _)) cats0. Qed.

Lemma sort_sorted (xs : seq A) : sorted cmp2 xs -> sorted cmplex (sort xs).
Proof. by rewrite /sort => H; apply merge_sort_rec_sorted. Qed.

End Mergesort.

End Mergesort_tailrec.

Require Import extraction_ocaml.
Set Extraction Flag 8175.

Extraction Implicit merge [T].
Extraction Implicit merge_sort_push [T].
Extraction Implicit merge_sort_pop [T].
Extraction Implicit merge_sort_rec [T].
Extraction Implicit sort [T].

Extraction Implicit Mergesort.merge [A].
Extraction Implicit Mergesort.merge_pair [A].
Extraction Implicit Mergesort.sort [A].

Extraction Implicit Mergesort_tailrec.merge [A].
Extraction Implicit Mergesort_tailrec.merge_sort_push [A].
Extraction Implicit Mergesort_tailrec.merge_sort_pop [A].
Extraction Implicit Mergesort_tailrec.merge_sort_rec [A].
Extraction Implicit Mergesort_tailrec.sort [A].

Extraction
  "../../ocaml/mergesort.ml"
  iota sort Mergesort.sort Mergesort_tailrec.sort.
