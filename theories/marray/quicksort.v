Require Import all_ssreflect fingroup perm core ordinal_ext Wf_nat.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Search.

Variable (I : finType) (A : Type) (f : A -> bool).

Definition up_search (i j : 'I_#|I|.+1) :
  i <= j -> AState {ffun I -> A} {k : 'I_#|I|.+1 | i <= k <= j} :=
  Fix
    (@well_founded_ordgt #|I|.+1)
    (fun i => i <= j -> AState {ffun I -> A} {k : 'I_#|I|.+1 | i <= k <= j})
    (fun (i : 'I_#|I|.+1) rec (H : i <= j) =>
       match i < j as cij return (i < j) = cij -> _ with
         | true => fun H' : i < j =>
           mlet x := astate_GET (ltnidx_l H') in
           if f x
           then astate_ret (exist (fun k : 'I_ _ => i <= k <= j) i
                  ltac:(by rewrite /= leqnn H))
           else mlet '(exist k Hk) := rec (ltnidx_ls H') (leqnn _) H' in
                astate_ret (exist (fun k : 'I_ _ => i <= k <= j) k
                  ltac:(by case/andP: Hk => /ltnW ->))
         | false => fun _ =>
           astate_ret (exist (fun k : 'I_ _ => i <= k <= j) j
             ltac:(by rewrite /= leqnn H))
       end (erefl (i < j)))
    i.

Variant up_search_spec (i j : 'I_#|I|.+1) (arr : {ffun I -> A}) :
  {k : 'I_#|I|.+1 | i <= k <= j} * {ffun I -> A} -> Prop :=
  UpSearchSpec (k : 'I_#|I|.+1) (Hk : i <= k <= j) :
  (forall k' : 'I_#|I|, k = k' :> nat -> k < j -> f (arr (fin_decode k'))) ->
  (forall i' : 'I_#|I|, i <= i' < k -> ~~ f (arr (fin_decode i'))) ->
  @up_search_spec i j arr (exist _ k Hk, arr).

Lemma run_up_search (i j : 'I_#|I|.+1) (arr : {ffun I -> A}) (Hij : i <= j) :
  up_search_spec arr (run_AState (up_search Hij) arr).
Proof.
rewrite /up_search /Fix.
elim/Acc_rect: i / (well_founded_ordgt i) (well_founded_ordgt i) Hij
  => i _ IH Hi Hij; rewrite -Fix_F_eq /=.
case: {2 3}(i < j) (erefl (i < j)) => H; rewrite !run_AStateE;
  first case: ifP => H0; rewrite ?run_AStateE.
- constructor=> [k' H1 H2 |]; first congr (f (arr (_ _))): H0; ssromega.
- case: {IH Hi} (IH (ltnidx_ls H)) => //= k /andP [] H1 H2 H3 H4;
    rewrite !run_AStateE; constructor=> // i';
    rewrite leq_eqVlt andb_orl => /orP [] H5; auto;
    congr (~~ (f (arr (_ _)))): (negbT H0); ssromega.
- constructor; ssromega.
Qed.

Definition down_search (i j : 'I_#|I|.+1) :
  j <= i -> AState {ffun I -> A} {k : 'I_#|I|.+1 | j <= k <= i} :=
  Fix
    (@well_founded_ordlt #|I|.+1)
    (fun i => j <= i -> AState {ffun I -> A} {k : 'I_#|I|.+1 | j <= k <= i})
    (fun (i : 'I_#|I|.+1) rec (H : j <= i) =>
       (if j < i as cij return (j < i) = cij -> _
        then fun H' : j < i =>
               mlet x := astate_GET (ltnidx_rp (ltnm0m H')) in
               if f x
               then astate_ret (exist (fun k : 'I_ _ => j <= k <= i) i
                                      ltac:(by rewrite /= H leqnn))
               else mlet '(exist k Hk) :=
                      rec (ord_pred' (i := i) (ltnm0m H'))
                          ltac:(by move/ltn_predK: (H') => ->)
                          ltac:(by case: (i) H' => -[]) in
                    astate_ret (exist (fun k : 'I_ _ => j <= k <= i) k
                      ltac:(by case/andP: Hk => -> /leq_trans;
                            apply; apply/leq_pred))
        else fun _ => astate_ret (exist (fun k : 'I_ _ => j <= k <= i) j
                        ltac:(by rewrite /= leqnn H)))
       (erefl (j < i)))
    i.

Variant down_search_spec (i j : 'I_#|I|.+1) (arr : {ffun I -> A}) :
  {k : 'I_#|I|.+1 | j <= k <= i} * {ffun I -> A} -> Prop :=
  DownSearchSpec (k : 'I_#|I|.+1) (Hk : j <= k <= i) :
  (forall k' : 'I_#|I|, k = k'.+1 :> nat -> j < k ->
                        f (arr (fin_decode k'))) ->
  (forall i' : 'I_#|I|, k <= i' < i -> ~~ f (arr (fin_decode i'))) ->
  @down_search_spec i j arr (exist _ k Hk, arr).

Lemma run_down_search (i j : 'I_#|I|.+1) (arr : {ffun I -> A}) (Hij : j <= i) :
  @down_search_spec i j arr (run_AState (down_search Hij) arr).
Proof.
rewrite /down_search /Fix.
elim/Acc_rect: i / (well_founded_ordlt i) (well_founded_ordlt i) Hij
  => i _ IH Hi Hji; rewrite -Fix_F_eq /=.
case: {2 3}(j < i) (erefl (j < i)) => H; rewrite !run_AStateE;
  first case: ifP => [| /negbT] H0; rewrite ?run_AStateE.
- constructor=> [k' H1 H2 |]; first congr (f (arr (_ _))): H0; ssromega.
- case: {IH} (IH (ord_pred' (ltnm0m H))) => [| k Hk H1 H2]; first ssromega.
  rewrite !run_AStateE; constructor=> // i' /andP [] H3.
  rewrite leq_eqVlt => /orP [] H4;
    [ congr (~~ (f (arr (_ _)))): H0 | apply H2 ]; ssromega.
- constructor; ssromega.
Qed.

End Search.

Module Quicksort.
Section Quicksort.

Variable
  (I : finType) (A : Type) (cmp : A -> A -> bool)
  (Hcmp_trans : transitive cmp) (Hcmp_asym : forall x y, ~~ cmp y x -> cmp x y).

Lemma Hcmp_refl x : cmp x x.
Proof. by case: (cmp x x) (@Hcmp_asym x x) => //; apply. Qed.

Definition partition (pivot : A) :
  forall (i j : 'I_#|I|.+1),
    i <= j -> AState {ffun I -> A} {k : 'I_#|I|.+1 | i <= k <= j} :=
  Fix
    (@well_founded_ordgt #|I|.+1)
    (fun i => forall j : 'I_#|I|.+1,
         i <= j -> AState {ffun I -> A} {k : 'I_#|I|.+1 | i <= k <= j})
    (fun (i : 'I_#|I|.+1) rec (j : 'I_#|I|.+1) (Hij : i <= j) =>
       mlet '(exist i' Hi) := up_search (cmp pivot) (i := i) (j := j) Hij in
       mlet '(exist j' Hj) :=
         down_search (xpredC (cmp pivot)) (i := j) (j := i) Hij in
       match i'.+1 < j' as cij return i'.+1 < j' = cij -> _ with
         | true => fun Hij : i'.+1 < j' =>
           SWAP (ltnidx_l (ltnW Hij)) (ltnidx_rp (ltnm0m Hij));;
           mlet '(exist k Hk) :=
             rec (ltnidx_ls (ltnW Hij))
                 ltac: (by case/andP: Hi; rewrite ltnS)
                 (ord_pred' (i := j') (ltnm0m Hij))
                 ltac: (by case: (j') Hij => -[]) in
           astate_ret (exist (fun k : 'I_ _ => i <= k <= j) k
             ltac:(move: Hi Hj Hk => /andP [Hi _] /andP [_ Hj] /andP [Hkl Hkr];
                   rewrite (leq_trans Hi (ltnW Hkl)) (leq_trans Hkr) //
                           (leq_trans (leq_pred _)) //))
         | false => fun _ =>
           astate_ret (exist (fun k : 'I_ _ => i <= k <= j) i' Hi)
       end (erefl (i'.+1 < j'))).

Variant partition_spec (pivot : A) (i j : 'I_#|I|.+1) (arr : {ffun I -> A}) :
  {k : 'I_#|I|.+1 | i <= k <= j} * {ffun I -> A} -> Prop :=
  PartitionSpec (p : {perm I}) (k : 'I_#|I|.+1) (Hk : i <= k <= j) :
  let arr' := perm_ffun p arr in
  perm_on [set ix | i <= fin_encode ix < j] p ->
  (forall ix : 'I_#|I|, i <= ix < j ->
                        cmp pivot (arr' (fin_decode ix)) = (k <= ix)) ->
  @partition_spec pivot i j arr (exist _ k Hk, arr').

Lemma run_partition
      (pivot : A) (i j : 'I_#|I|.+1) (Hij : i <= j) (arr : {ffun I -> A}) :
  @partition_spec pivot i j arr (run_AState (partition pivot Hij) arr).
Proof with rewrite ?run_AStateE.
rewrite /partition /Fix.
elim/Acc_rect: i / (well_founded_ordgt i) (well_founded_ordgt i) j Hij arr
  => /= i _ IH Hi j Hij arr; rewrite -Fix_F_eq /=...
case: run_up_search => i' Hi'0 Hi'1 Hi'2...
case: run_down_search => j' Hj'0 Hj'1 Hj'2...
case: {2 3}(i'.+1 < j') (erefl (i'.+1 < j')) => [Hij' | /negbT];
  rewrite -?leqNgt !(run_SWAP, run_AStateE).
- case: {IH} (IH (ltnidx_ls _) _ _ (ord_pred' _)); first ssromega;
    move=> p k Hk arr' /=...
  have {arr'} ->:
       arr' = [ffun ix =>
               arr ((p * tperm (fin_decode (ltnidx_l (ltnW Hij')))
                               (fin_decode (ltnidx_rp (ltnm0m Hij'))))%g ix)]
    by apply/ffunP => ix; rewrite !ffunE permM.
  set arr' := [ffun ix => arr _] => Hp Hpart; constructor.
  + rewrite perm_onM //; [ apply/(subset_trans Hp) | ]; apply/subsetP => ix;
      rewrite !inE; first ssromega.
    rewrite -(inj_eq (@fin_encode_inj _)) (inj_tperm _ _ _ (@fin_encode_inj _))
            !fin_decodeK; case: tpermP; ssromega.
  + move=> ix /andP [H H0]; case: (boolP (i' < ix < j'.-1)) => [/Hpart // | H1].
    rewrite ffunE permE /= (out_perm Hp) ?inE ?fin_decodeK //
            -(inj_tperm _ _ _ (@fin_decode_inj _)).
    move: (Hj'1 (ltnidx_rp (ltnm0m Hij'))) (Hi'1 (ltnidx_l (ltnW Hij')))
          (Hi'2 ix) (Hj'2 ix); case: tpermP; ssromega.
- rewrite leq_eqVlt ltnS -{2}(perm_ffunE1 arr) => Hij'; constructor;
    rewrite ?perm_on1 //= => ix /andP [H H0]; rewrite ffunE permE.
  case/predU1P: Hij' => Hij'; last by move: (Hi'2 ix) (Hj'2 ix); ssromega.
  have Hij'' : i' < j' by rewrite Hij'.
  move: (Hi'1 (ltnidx_l Hij'') erefl) (Hj'1 (ltnidx_l Hij'') Hij'); ssromega.
Qed.

Definition quicksort_rec :
  'I_#|I|.+1 -> 'I_#|I|.+1 -> AState {ffun I -> A} unit :=
  Fix
  (@well_founded_ordgt #|I|.+1)
  (fun _ => 'I_#|I|.+1 -> AState {ffun I -> A} unit)
  (fun (i : 'I_#|I|.+1) recl =>
     Fix
     (@well_founded_ordlt #|I|.+1)
     (fun _ => AState {ffun I -> A} unit)
     (fun (j : 'I_#|I|.+1) recr =>
        match i.+1 < j as cij return i.+1 < j = cij -> _ with
          | true => fun Hij : i.+1 < j =>
            let i' := ltnidx_l (ltnW Hij) in
            let si := ltnidx_ls (ltnW Hij) in
            mlet pivot := astate_GET i' in
            mlet '(exist k Hk) := @partition pivot si j (ltnW Hij) in
            let Hk' : 0 < k := ltac:(by case/andP: Hk => /ltnm0m) in
            let pk := ltnidx_rp (j := k) Hk' in
            mlet x := astate_GET pk in
            astate_SET i' x;; astate_SET pk pivot;;
            recr (ord_pred' (i := k) Hk')
                 ltac:(by case/andP: (Hk); rewrite /= (ltn_predK Hk'));;
            recl k ltac:(by case/andP: (Hk)) j
          | false => fun _ => astate_ret tt
        end (erefl (i.+1 < j)))).

Definition quicksort : AState {ffun I -> A} unit :=
  quicksort_rec ord0 (@Ordinal #|I|.+1 $|I| ltac:(by rewrite raw_cardE)).

Variant quicksort_rec_spec (i j : 'I_#|I|.+1) (arr : {ffun I -> A}) :
  unit * {ffun I -> A} -> Prop :=
  QuicksortRecSpec (p : {perm I}) :
  let arr' := perm_ffun p arr in
  perm_on [set ix | i <= fin_encode ix < j] p ->
  (forall ix ix' : 'I_#|I|,
    i <= ix -> ix <= ix' -> ix' < j ->
    cmp (arr' (fin_decode ix)) (arr' (fin_decode ix'))) ->
  quicksort_rec_spec i j arr (tt, arr').

Lemma QuicksortRecSpec_
      (i j : 'I_#|I|.+1) (arr : {ffun I -> A}) (p : {perm I}) :
  let arr' := perm_ffun p arr in
  perm_on [set ix | i <= fin_encode ix & fin_encode ix < j] p ->
  (forall ix ix' : 'I_#|I|,
    i <= ix -> ix < ix' -> ix' < j ->
    cmp (arr' (fin_decode ix)) (arr' (fin_decode ix'))) ->
  quicksort_rec_spec i j arr (tt, arr').
Proof.
by simpl=> H H'; constructor=> // ix ix' ?;
  rewrite leq_eqVlt => /predU1P [/ord_inj <- | ?] ?;
  [ apply Hcmp_refl | apply H' ].
Qed.

Lemma run_quicksort_rec (i j : 'I_#|I|.+1) (arr : {ffun I -> A}) :
  quicksort_rec_spec i j arr (run_AState (quicksort_rec i j) arr).
Proof with rewrite ?run_AStateE.
rewrite /quicksort_rec /Fix.
elim/Acc_rect: i / (well_founded_ordgt i) (well_founded_ordgt i) j arr =>
  i _ IHi Hi j arr; rewrite -Fix_F_eq /=.
elim/Acc_rect: j / (well_founded_ordlt j) (well_founded_ordlt j) arr =>
  j _ IHj Hj arr; rewrite -Fix_F_eq /=.
case: {2 3}(i.+1 < j) (erefl (i.+1 < j)) => [| /negbT];
  rewrite -/(is_true _) -?leqNgt => Hij; rewrite !run_AStateE /=;
  last by rewrite -{2}(perm_ffunE1 arr);
          apply QuicksortRecSpec_; rewrite ?perm_on1 //; ssromega.
case: (run_partition _ (i := ltnidx_ls (ltnW Hij))) => /= pp k Hk...
set ix_pivot := ltnidx_l (ltnW Hij).
set ix_part := ltnidx_rp _.
set arr' := ffun_set _ _ _.
move=> Hpp Hpart.
have {arr'} ->:
  arr' = perm_ffun (tperm (fin_decode ix_part) (fin_decode ix_pivot) * pp) arr
  by apply/ffunP => ix; rewrite !ffunE permM permE /=;
     do !case: eqP => // _; rewrite (out_perm Hpp) // inE fin_decodeK; ssromega.
case: {IHj} (IHj (ord_pred' _)); first by ssromega.
rewrite /= /predn' => /= pl Hpl Hsortl.
case: IHi => [| pr arr' Hpr]; first by case/andP: (Hk).
subst arr'; rewrite -!perm_ffunEM mulgA => Hsortr.
apply QuicksortRecSpec_ => [| ix ix' H H0 H1]; first by
  do !apply perm_onM; [ apply (subset_trans Hpr) | apply (subset_trans Hpl) | |
                        apply (subset_trans Hpp) ];
  apply/subsetP => x; rewrite !inE; try ssromega;
  case: tpermP; rewrite ?eqxx => // -> _; rewrite fin_decodeK; ssromega.
rewrite !ffunE !permM.
case: (ltngtP ix ix_part) (ltngtP ix' ix_part) => H2 [] H3; try ssromega.
- rewrite !(out_perm Hpr); try by rewrite inE fin_decodeK; ssromega.
  by move: (Hsortl ix ix'); rewrite !ffunE !permM; apply; ssromega.
- rewrite (out_perm Hpr); last by rewrite inE fin_decodeK; ssromega.
  move: (perm_closed (fin_decode ix) Hpl) (perm_closed (fin_decode ix') Hpr);
    rewrite !inE !fin_decodeK => H4 H5.
  rewrite (out_perm (x := pr _) Hpl); last by rewrite !inE; ssromega.
  apply Hcmp_trans with (arr (fin_decode ix_pivot)); first apply Hcmp_asym;
    rewrite -(fin_encodeK (tperm _ _ _)) -(ffunE (fun ix => arr (pp ix))) Hpart
            (inj_tperm _ _ _ (@fin_encode_inj _)) !fin_decodeK;
    case: tpermP; ssromega.
- move/ord_inj in H3; subst ix' => {H2}.
  rewrite !(out_perm Hpr, out_perm (x := _ ix_part) Hpl, tpermL,
            out_perm (x := _ ix_pivot) Hpp);
    try by rewrite inE fin_decodeK; ssromega.
  move: (perm_closed (fin_decode ix) Hpl); rewrite !inE fin_decodeK /= => H2.
  apply Hcmp_asym.
  rewrite -[X in pp X]fin_encodeK -(ffunE (fun ix => arr (pp ix))) Hpart
          (inj_tperm _ _ _ (@fin_encode_inj _)) !fin_decodeK;
    case: tpermP; ssromega.
- move: (Hsortr ix ix'); rewrite !ffunE !permM; apply; ssromega.
- move/ord_inj in H2; subst ix => {H3}.
  move: (perm_closed (fin_decode ix') Hpr); rewrite !inE !fin_decodeK => H2.
  rewrite (out_perm Hpr) ?(out_perm Hpl) ?tpermL 1?(out_perm Hpp);
    try by rewrite ?inE ?fin_decodeK; ssromega.
  rewrite -(fin_encodeK (pr _)) -(inj_tperm _ _ _ (@fin_decode_inj _))
          -(ffunE (fun ix => arr (pp ix))) tpermD ?Hpart; ssromega.
Qed.

Variant quicksort_spec (arr : {ffun I -> A}) : unit * {ffun I -> A} -> Prop :=
  QuicksortSpec (p : {perm I}) :
  let arr' := perm_ffun p arr in
  (forall ix ix' : 'I_#|I|,
    ix <= ix' -> cmp (arr' (fin_decode ix)) (arr' (fin_decode ix'))) ->
  quicksort_spec arr (tt, arr').

Lemma run_quicksort (arr : {ffun I -> A}) :
  quicksort_spec arr (run_AState quicksort arr).
Proof.
rewrite /quicksort.
set j := Ordinal _.
have ->: j = ord_max by apply/ord_inj => /=; rewrite raw_cardE.
by case: run_quicksort_rec => p /= Hp Hsort; constructor=> *; apply: Hsort.
Qed.

Definition quicksort_ (arr : {ffun I -> A}) : {ffun I -> A} :=
  (run_AState quicksort arr).2.

End Quicksort.
End Quicksort.

Require Import extraction_ocaml.

Extraction Implicit Quicksort.partition [I].
Extraction Implicit Quicksort.quicksort_rec [I].

Extraction Inline negb up_search down_search Quicksort.quicksort.

Set Extraction Flag 2031.
Extract Type Arity AState 0.

Extraction "../../ocaml/quicksort_o0.ml" nat_eqType ordinal_finType Quicksort.

Set Extraction Flag 8175.
Extract Type Arity AState 1.

Extraction "../../ocaml/quicksort.ml" nat_eqType ordinal_finType Quicksort.
