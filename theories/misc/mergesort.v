Require Import all_ssreflect all_algebra reflection_base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Perm.

Variable (A : eqType) (le : A -> A -> bool).

Definition condrev (r : bool) (xs : seq A) :=
  if r then rev xs else xs.

Lemma perm_catrev (xs ys : seq A) : perm_eq (catrev xs ys) (xs ++ ys).
Proof. by rewrite catrevE perm_cat2r perm_eq_sym perm_eq_rev. Qed.

Lemma perm_condrev (r : bool) (xs : seq A) : perm_eq (condrev r xs) xs.
Proof. by case: r => //=; rewrite perm_eq_sym perm_eq_rev. Qed.

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

Fixpoint flatten_map (A B : Type) (f : A -> seq B) (xs : seq A) : seq B :=
  if xs is x :: xs' then f x ++ flatten_map f xs' else [::].

Lemma flatten_mapE (A B : Type) (f : A -> seq B) (xs : seq A) :
  flatten_map f xs = flatten (map f xs).
Proof. by elim: xs => //= x xs <-. Qed.

Lemma perm_flatten_map (A B : eqType) (f : A -> seq B) (xs ys : seq A) :
  perm_eq xs ys -> perm_eq (flatten_map f xs) (flatten_map f ys).
Proof. by rewrite !flatten_mapE => H; apply/perm_flatten/perm_map. Qed.

Inductive Seq : Type :=
  | SeqAtom   of rindex
  | SeqNil
  | SeqCat    of Seq & Seq
  | SeqCatrev of Seq & Seq
  | SeqRev    of Seq.

Fixpoint denote_Seq (A : Type) (f : rindex -> seq A) (xs : Seq) : seq A :=
  match xs with
    | SeqAtom xs => f xs
    | SeqNil => [::]
    | SeqCat xs ys => denote_Seq f xs ++ denote_Seq f ys
    | SeqCatrev xs ys => catrev (denote_Seq f xs) (denote_Seq f ys)
    | SeqRev xs => rev (denote_Seq f xs)
  end.

Fixpoint denote_eqs1 (A : eqType) (f : rindex -> seq A)
                     (xs : seq (bool * Seq * Seq)) : Type :=
  match xs with
    | [::] => unit
    | (peq, ys, zs) :: xs' =>
      denote_eqs1 f xs' * (peq = perm_eq (denote_Seq f ys) (denote_Seq f zs))
  end.

Fixpoint denote_eqs2 (A : eqType) (f : rindex -> seq A)
                     (xs : seq (bool * seq rindex * seq rindex)) : Type :=
  match xs with
    | [::] => unit
    | [:: (peq, ys, zs)] => peq = perm_eq (flatten_map f ys) (flatten_map f zs)
    | (peq, ys, zs) :: xs' =>
      denote_eqs2 f xs' * (peq = perm_eq (flatten_map f ys) (flatten_map f zs))
  end.

Fixpoint sort_Seq_rec (xs : Seq) (xss : seq (seq rindex)) : seq (seq rindex) :=
  match xs with
    | SeqAtom i => merge_sort_push leq_rindex [:: i] xss
    | SeqNil => xss
    | SeqCat xs ys | SeqCatrev xs ys => sort_Seq_rec ys (sort_Seq_rec xs xss)
    | SeqRev xs => sort_Seq_rec xs xss
  end.

Definition sort_Seq (xs : Seq) : seq rindex :=
  merge_sort_pop leq_rindex [::] (sort_Seq_rec xs [::]).

Definition perm_eqs_norm :
  seq (bool * Seq * Seq) -> seq (bool * seq rindex * seq rindex) :=
  map (fun '(peq, xs, ys) =>
         let (xs', ys') := perm_elim leq_rindex (sort_Seq xs) (sort_Seq ys) in
         (peq, xs', ys')).

Section Sort_ext.

Variable (T : eqType) (leT : rel T).

Lemma merge_sort_push_perm (xs : seq T) (yss : seq (seq T)) :
  perm_eq (flatten (merge_sort_push leT xs yss)) (xs ++ flatten yss).
Proof.
elim: yss xs => //= -[| y ys] yss IH xs //=.
by rewrite (perm_eqlP (IH _)) -cat_cons catA perm_cat2r perm_merge.
Qed.

Lemma merge_sort_pop_perm (xs : seq T) (yss : seq (seq T)) :
  perm_eq (merge_sort_pop leT xs yss) (xs ++ flatten yss).
Proof.
elim: yss xs => [| ys yss IH] xs; rewrite ?cats0 //=.
by rewrite (perm_eqlP (IH _)) catA perm_cat2r perm_merge.
Qed.

End Sort_ext.

Lemma sort_Seq_perm (A : eqType) (f : rindex -> seq A) (xs : Seq) :
  perm_eq (flatten_map f (sort_Seq xs)) (denote_Seq f xs).
Proof.
move: (merge_sort_pop_perm leq_rindex [::] (sort_Seq_rec xs [::])).
rewrite /sort_Seq => /= /(perm_flatten_map f) /perm_eqlP ->.
rewrite -[denote_Seq _ _]cats0 -[X in _ ++ X]/(flatten_map f (flatten [::])).
elim: xs [::] => [i | | xs IHx ys IHy | xs IHx ys IHy | xs IH] xss //=;
  try rewrite -?(perm_eqrP (IHy _)).
- by move: (merge_sort_push_perm leq_rindex [:: i] xss)
    => /= /(perm_flatten_map f) /perm_eqlP ->.
- by rewrite (perm_eqlP (IHy _)) perm_eq_sym -catA perm_catCA perm_cat2l
             perm_eq_sym IHx.
- by rewrite (perm_eqlP (IHy _)) perm_eq_sym catrevE -catA perm_catCA perm_cat2l
             perm_eq_sym (perm_eqlP (IHx _)) perm_cat2r perm_eq_rev.
- by rewrite (perm_eqlP (IH _)) perm_cat2r perm_eq_rev.
Qed.

Lemma perm_eqs_normE
      (A : eqType) (f : rindex -> seq A) (xs : seq (bool * Seq * Seq)) :
  denote_eqs1 f xs -> denote_eqs2 f (perm_eqs_norm xs).
Proof.
by elim: xs => [| [[b ys] zs] [| x xs] IH] //=;
  case: (perm_elim _ _ _) (perm_elim_perm leq_rindex (sort_Seq ys) (sort_Seq zs))
    => /= ys' zs' [];
  rewrite -(perm_eqlP (sort_Seq_perm _ _)) -(perm_eqrP (sort_Seq_perm _ _)) =>
    /(perm_flatten_map f) /perm_eqlP -> /(perm_flatten_map f) /perm_eqrP ->;
  rewrite !flatten_mapE !map_cat !flatten_cat perm_cat2l;
  case => // Hl Hr; split => //; apply IH.
Qed.

Ltac tag_seq tag xs :=
  lazymatch xs with
    | @nil ?A => constr:(xs)
    | ?x :: ?xs => let xs' := tag_seq tag xs in constr:(tag [:: x] ++ xs')
    | rcons ?xs ?x => let xs' := tag_seq tag xs in constr:(xs' ++ tag [:: x])
    | ?xs ++ ?ys =>
      let xs' := tag_seq tag xs in
      let ys' := tag_seq tag ys in
      constr:(xs' ++ ys')
    | catrev ?xs ?ys =>
      let xs' := tag_seq tag xs in
      let ys' := tag_seq tag ys in
      constr:(catrev xs' ys')
    | rev ?xs => let xs' := tag_seq tag xs in constr:(rev xs')
    | _ => constr:(tag xs)
  end.

Ltac tag_permeqs A tag eqs :=
  let tag_permeq xs ys :=
    let xs' := tag_seq tag xs in
    let ys' := tag_seq tag ys in constr: (perm_eq xs' ys')
  in
  let rec tag_rec eqs' :=
    let peq := fresh "peq" in
    lazymatch goal with
      | |- context [@perm_eq A ?xs ?ys] =>
        let peq' := tag_permeq xs ys in
        set peq := (perm_eq _ _); tag_rec (eqs' * (peq = peq'))%type
      | H : context [@perm_eq A ?xs ?ys] |- _ =>
        let peq' := tag_permeq xs ys in
        set peq := (perm_eq _ _) in H; tag_rec (eqs' * (peq = peq'))%type
      | _ =>
        set eqs := eqs'
    end
  in
  tag_rec unit.

Ltac reify_eqs f E :=
  let rec reify e :=
    lazymatch e with
      | f ?i => constr: (SeqAtom i)
      | @nil _ => constr: (SeqNil)
      | ?el ++ ?er =>
        let el' := reify el in
        let er' := reify er in
        constr: (SeqCat el' er')
      | catrev ?el ?er =>
        let el' := reify el in
        let er' := reify er in
        constr: (SeqCatrev el' er')
      | rev ?e' => let e'' := reify e' in constr: (SeqRev e'')
    end
  in
  lazymatch E with
    | (?E' * (?peq = perm_eq ?xs ?ys))%type =>
      let E'' := reify_eqs f E' in
      let xs' := reify xs in
      let ys' := reify ys in
      constr: ((peq, xs', ys') :: E'')
    | unit =>
      constr: (@nil (bool * Seq * Seq))
  end.

Ltac perm_norm A f tag eqs :=
  myquote f eqs tag (@nil A);
  unfold tag in eqs;
  lazymatch goal with
    | eqs := ?eqs' |- _ =>
      let eqs'' := reify_eqs f eqs' in
      clear tag eqs;
      have/perm_eqs_normE eqs: denote_eqs1 f eqs'' by repeat
        split;
        lazymatch goal with
          |- ?peq = _ => rewrite /peq -?cats1; reflexivity
        end
  end;
  cbv [perm_eqs_norm map] in eqs;
  repeat
     (let pe := fresh "pe" in set pe := perm_elim _ _ _ in eqs;
     native_compute in pe; subst pe);
  cbv [denote_eqs2] in eqs.

Ltac autoperm :=
  let perm_eq' := fresh "perm_eq'" in pose perm_eq' := @perm_eq;
  let do_autoperm A :=
    let f := fresh "f" in pose f := tt;
    let tag := fresh "tag" in pose tag := (fun x : seq A => x);
    let eqs := fresh "eqs" in tag_permeqs A tag eqs;
    perm_norm A f tag eqs;
    cbv [flatten_map] in eqs;
    rewrite ?cats0 /= {f} in eqs;
    fold perm_eq' in eqs;
    move: eqs;
    repeat lazymatch goal with
      | |- _ * _ -> _ => case
      | |- ?peq = _ -> _ =>
        let H := fresh "H" in
        move: peq => peq H; subst peq
    end
  in
  repeat lazymatch goal with
    | |- context [@perm_eq ?A ?xs ?ys] => do_autoperm A
    | H : context [@perm_eq ?A ?xs ?ys] |- _ => do_autoperm A
  end;
  subst perm_eq';
  try by [].

Module PermExamples.

Example ex1 (A : eqType) (x y z : A) (xs ys zs zs' : seq A) :
  perm_eq (xs ++ zs) (zs' ++ xs) ->
  perm_eq (rcons xs x ++ y :: ys ++ z :: zs)
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
