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
           x <- astate_GET (ltnidx_l H');
           if f x
           then astate_ret (exist (fun k : 'I_ _ => i <= k <= j) i
                  ltac:(by rewrite /= leqnn H))
           else k <- rec (ltnidx_ls H') (leqnn _) H';
                let: (exist k Hk) := k in
                astate_ret (exist (fun k : 'I_ _ => i <= k <= j) k
                  ltac:(by case/andP: Hk => /ltnW -> ->))
         | false => fun _ =>
           astate_ret (exist (fun k : 'I_ _ => i <= k <= j) j
             ltac:(by rewrite /= leqnn H))
       end (erefl (i < j)))
    i.

Variant up_search_spec (i j : 'I_#|I|.+1) (arr : {ffun I -> A}) :
  {k : 'I_#|I|.+1 | i <= k <= j} * {ffun I -> A} -> Type :=
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
- by constructor; try ssromega;
    move=> k' H1 H2; congr (f (arr (_ _))): H0; apply/ord_inj.
- by case: {IH Hi} (IH (ltnidx_ls H)) => //= k /andP [] H1 H2 H3 H4;
    rewrite !run_AStateE; constructor=> // i';
    rewrite leq_eqVlt andb_orl => /orP []; auto=> /andP [] /eqP Hii' _;
    congr (~~ (f (arr (_ _)))): (negbT H0); apply ord_inj.
- by move/negbT/(conj Hij)/andP: H;
    rewrite -leqNgt -eqn_leq => /eqP/ord_inj Hij';
    subst j; constructor; ssromega.
Qed.

Definition down_search (i j : 'I_#|I|.+1) :
  j <= i -> AState {ffun I -> A} {k : 'I_#|I|.+1 | j <= k <= i} :=
  Fix
    (@well_founded_ordlt #|I|.+1)
    (fun i => j <= i -> AState {ffun I -> A} {k : 'I_#|I|.+1 | j <= k <= i})
    (fun (i : 'I_#|I|.+1) rec (H : j <= i) =>
       (if j < i as cij return (j < i) = cij -> _
        then fun H' : j < i =>
               x <- astate_GET (ltnidx_rp (ltnm0m H'));
               if f x
               then astate_ret (exist (fun k : 'I_ _ => j <= k <= i) i
                                      ltac:(by rewrite /= H leqnn))
               else k <- rec (ord_pred' (i := i) (ltnm0m H'))
                             ltac:(by move/ltn_predK: (H') => ->)
                             ltac:(by simpl; case: (nat_of_ord i) H');
                    let: (exist k Hk) := k in
                    astate_ret (exist (fun k : 'I_ _ => j <= k <= i) k
                      ltac:(by case/andP: Hk => -> /leq_trans;
                            apply; apply /leq_pred))
        else fun _ => astate_ret (exist (fun k : 'I_ _ => j <= k <= i) j
                        ltac:(by rewrite /= leqnn H)))
       (erefl (j < i)))
    i.

Variant down_search_spec (i j : 'I_#|I|.+1) (arr : {ffun I -> A}) :
  {k : 'I_#|I|.+1 | j <= k <= i} * {ffun I -> A} -> Type :=
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
- by constructor; try ssromega; move=> k' H1 H2;
    congr (f (arr (_ _))): H0; apply/ord_inj; rewrite /= /predn' H1.
- case: {IH} (IH (ord_pred' (ltnm0m H)));
    first by simpl; case: (nat_of_ord i) H {H0}.
  move=> k Hk H1 H2; rewrite !run_AStateE; constructor => // i' /andP [] H3.
  rewrite -(ltn_predK H) ltnS leq_eqVlt => /orP [/eqP |] H4.
  + by congr (~~ (f (arr (_ _)))): H0; apply/ord_inj; rewrite H4.
  + by apply H2; rewrite H3.
- move/negbT/(conj Hji)/andP: H;
    rewrite -leqNgt -eqn_leq => /eqP /ord_inj Hji';
    subst j; constructor; ssromega.
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
    i < j -> AState {ffun I -> A} {k : 'I_#|I|.+1 | i <= k <= j} :=
  Fix
    (@well_founded_ordgt #|I|.+1)
    (fun i => forall j : 'I_#|I|.+1,
         i < j -> AState {ffun I -> A} {k : 'I_#|I|.+1 | i <= k <= j})
    (fun (i : 'I_#|I|.+1) rec (j : 'I_#|I|.+1) (Hij : i < j) =>
       i' <- up_search (cmp pivot) (i := i) (j := j) (ltnW Hij);
       j' <- down_search (xpredC (cmp pivot)) (i := j) (j := i) (ltnW Hij);
       let: (exist i' Hi) := i' in
       let: (exist j' Hj) := j' in
       match i' < j' as cij return i' < j' = cij -> _ with
         | true => fun Hij : i' < j' =>
           SWAP (ltnidx_l Hij) (ltnidx_rp (ltnm0m Hij));;
           match i'.+2 < j' as cij return i'.+2 < j' = cij -> _ with
             | true => fun Hij' : i'.+2 < j' =>
               k <- rec
                 (ltnidx_ls Hij)
                 ltac:(by case/andP: Hi; rewrite ltnS)
                 (ord_pred' (i := j') (ltnm0m Hij))
                 ltac:(by rewrite /= /predn'; case: (nat_of_ord j') Hij');
               let: (exist k Hk) := k in
               astate_ret (exist (fun k : 'I_ _ => i <= k <= j) k
                 ltac:(by move: Hi Hj Hk
                           => /andP [Hi _] /andP [_ Hj] /andP [Hkl Hkr];
                         rewrite (leq_trans Hi (ltnW Hkl)) (leq_trans Hkr) //
                                 (leq_trans (leq_pred _))))
             | false => fun H : (i'.+2 < j') = false =>
               astate_ret
                 (exist (fun k : 'I_ _ => i <= k <= j) (ltnidx_ls Hij)
                        ltac:(by case/andP: Hi Hj => /leqW -> _ /andP [] _;
                                 apply leq_trans))
           end (erefl (i'.+2 < j'))
         | false => fun _ =>
           astate_ret (exist (fun k : 'I_ _ => i <= k <= j) i' Hi)
       end (erefl (i' < j'))).

Variant partition_spec (pivot : A) (i j : 'I_#|I|.+1) (arr : {ffun I -> A}) :
  {k : 'I_#|I|.+1 | i <= k <= j} * {ffun I -> A} -> Type :=
  PartitionSpec (p : {perm I}) (k : 'I_#|I|.+1) (Hk : i <= k <= j) :
  let arr' := [ffun ix => arr (p ix)] in
  perm_on [set ix | i <= fin_encode ix < j] p ->
  (forall ix : 'I_#|I|, i <= ix < j ->
                        cmp pivot (arr' (fin_decode ix)) = (k <= ix)) ->
  @partition_spec pivot i j arr (exist _ k Hk, arr').

Lemma run_partition
      (pivot : A) (i j : 'I_#|I|.+1) (Hij : i < j) (arr : {ffun I -> A}) :
  @partition_spec pivot i j arr (run_AState (partition pivot Hij) arr).
Proof with rewrite ?run_AStateE.
rewrite /partition /Fix.
have Hid_arr (arr' : {ffun I -> A}):
  arr' = [ffun ix => arr' ((1%g : {perm I}) ix)]
  by apply/ffunP => ix; rewrite ffunE permE.
elim/Acc_rect: i / (well_founded_ordgt i) (well_founded_ordgt i) j Hij arr
  => /= i _ IH Hi j Hij arr; rewrite -Fix_F_eq /=...
case: run_up_search => i' Hi'0 Hi'1 Hi'2...
case: run_down_search => j' Hj'0 Hj'1 Hj'2...
case: {2 3}(i' < j') (erefl (i' < j')) => [| /negbT];
  rewrite -?leqNgt => Hij'; rewrite !(run_SWAP, run_AStateE);
  last by rewrite {2}(Hid_arr arr); constructor; rewrite ?perm_on1 //= => ix;
          rewrite ffunE permE => /andP [H H0]; case: leqP => H1;
          last (by apply/negbTE/Hi'2; rewrite H);
          rewrite -(negbK (cmp _ _)) Hj'2 // H0 (leq_trans Hij').
case: {2 3}(i'.+2 < j') (erefl (i'.+2 < j')) => [| /negbT];
  rewrite -/(is_true _) -?leqNgt => Hij''; rewrite !run_AStateE.
- case: {IH} (IH (ltnidx_ls Hij') _ _ (ord_pred' _)) => [| p k Hk arr' /=];
    first by rewrite /= ltnS; case/andP: Hi'0...
  have {arr'} ->:
       arr' = [ffun ix =>
               arr ((p * tperm (fin_decode (ltnidx_l Hij'))
                               (fin_decode (ltnidx_rp (ltnm0m Hij'))))%g ix)]
    by apply/ffunP => ix; rewrite !ffunE permM.
  set arr' := [ffun ix => arr _] => Hp Hpart; constructor.
  + rewrite perm_onM //; [ apply/(subset_trans Hp) | ]; apply/subsetP => ix;
      rewrite !inE; try ssromega.
    move/eqP; case: tpermP => // /eqP;
      rewrite -(can2_eq (@fin_encodeK _) (@fin_decodeK _)) => /eqP -> _ //=;
      ssromega.
  + move=> ix /andP [H H0];
      case: (boolP (i' < ix < j'.-1)) => [/Hpart -> // | H1]; apply/esym.
    rewrite ffunE permE /= (out_perm Hp) ?inE ?fin_decodeK // permE /=
            !(inj_eq (@fin_decode_inj _)) -!(inj_eq (@ord_inj _)) /=.
    case: eqP => H2; last case: eqP => H3.
    * rewrite -(negbK (cmp _ _)) Hj'1; ssromega.
    * rewrite Hi'1; ssromega.
    * case/nandP: H1; rewrite -leqNgt -(negbK (cmp _ _)) => H4;
        [ rewrite Hi'2 | rewrite Hj'2 ]; ssromega.
- constructor.
  + apply/subsetP => ix; rewrite !inE => /eqP; case: tpermP => // /eqP;
      rewrite -(can2_eq (@fin_encodeK _) (@fin_decodeK _)) => /eqP -> _ //=;
      ssromega.
  + move=> ix /andP [H H0]; apply/esym.
    rewrite ffunE permE /= !(inj_eq (@fin_decode_inj _))
            -!(inj_eq (@ord_inj _)) /=.
    case: eqP => H1; last case: eqP => H2.
    * rewrite -(negbK (cmp _ _)) Hj'1; ssromega.
    * rewrite Hi'1; ssromega.
    * move/eqP: H1; rewrite neq_ltn -(negbK (cmp _ _)) => /orP [] H1;
        [ rewrite Hi'2 | rewrite Hj'2 ]; ssromega.
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
            pivot <- astate_GET i';
            k <- @partition pivot si j Hij;
            let: (exist k Hk) := k in
            let Hk' : 0 < k := ltac:(by case/andP: Hk => /ltnm0m) in
            let pk := ltnidx_rp (j := k) Hk' in
            x <- astate_GET pk; astate_SET i' x;; astate_SET pk pivot;;
            recr (ord_pred' (i := k) Hk')
                 ltac:(by case/andP: (Hk); rewrite /= (ltn_predK Hk'));;
            recl k ltac:(by case/andP: (Hk)) j
          | false => fun _ => astate_ret tt
        end (erefl (i.+1 < j)))).

Definition quicksort : AState {ffun I -> A} unit :=
  quicksort_rec ord0 (@Ordinal #|I|.+1 $|I| ltac:(by rewrite cardT')).

Variant quicksort_rec_spec (i j : 'I_#|I|.+1) (arr : {ffun I -> A}) :
  unit * {ffun I -> A} -> Type :=
  QuicksortRecSpec (p : {perm I}) :
  let arr' := [ffun ix => arr (p ix)] in
  perm_on [set ix | i <= fin_encode ix < j] p ->
  (forall ix ix' : 'I_#|I|,
    i <= ix -> ix <= ix' -> ix' < j ->
    cmp (arr' (fin_decode ix)) (arr' (fin_decode ix'))) ->
  quicksort_rec_spec i j arr (tt, arr').

Lemma QuicksortRecSpec_
      (i j : 'I_#|I|.+1) (arr : {ffun I -> A}) (p : {perm I}) :
  let arr' := [ffun ix => arr (p ix)] in
  perm_on [set ix | i <= fin_encode ix & fin_encode ix < j] p ->
  (forall ix ix' : 'I_#|I|,
    i <= ix -> ix < ix' -> ix' < j ->
    cmp (arr' (fin_decode ix)) (arr' (fin_decode ix'))) ->
  quicksort_rec_spec i j arr (tt, arr').
Proof.
by simpl=> H H'; constructor => // ix ix' ?;
  rewrite leq_eqVlt => /predU1P [/ord_inj <- | ?] ?;
  [ apply Hcmp_refl | apply H' ].
Qed.

Lemma run_quicksort_rec (i j : 'I_#|I|.+1) (arr : {ffun I -> A}) :
  quicksort_rec_spec i j arr (run_AState (quicksort_rec i j) arr).
Proof with rewrite ?run_AStateE.
rewrite /quicksort_rec /Fix.
have Hid_arr (arr' : {ffun I -> A}):
  arr' = [ffun ix => arr' ((1%g : {perm I}) ix)]
  by apply/ffunP => ix; rewrite ffunE permE.
elim/Acc_rect: i / (well_founded_ordgt i) (well_founded_ordgt i) j arr =>
  i _ IHi Hi j arr; rewrite -Fix_F_eq /=.
elim/Acc_rect: j / (well_founded_ordlt j) (well_founded_ordlt j) arr =>
  j _ IHj Hj arr; rewrite -Fix_F_eq /=.
case: {2 3}(i.+1 < j) (erefl (i.+1 < j)) => [| /negbT];
  rewrite -/(is_true _) -?leqNgt => Hij; rewrite !run_AStateE /=;
  last by rewrite {2}(Hid_arr arr);
          apply QuicksortRecSpec_; rewrite ?perm_on1 //; ssromega.
case: (run_partition _ (i := ltnidx_ls (ltnW Hij))) => /= pp k Hk...
set ix_pivot := ltnidx_l (ltnW Hij).
set ix_part := ltnidx_rp _.
set arr' := ffun_set _ _ _.
move=> Hpp Hpart.
have {arr'} ->:
     arr' = [ffun ix => arr ((tperm (fin_decode ix_part)
                                    (fin_decode ix_pivot) * pp)%g ix)] by
  apply/ffunP => ix; rewrite !ffunE permM permE /=;
  do !case: eqP => // _; rewrite (out_perm Hpp) // inE fin_decodeK; ssromega.
case: {IHj} (IHj (ord_pred' _)); first by move=> {ix_part}; ssromega.
rewrite /= /predn' => /= pl Hpl Hsortl.
case: IHi; first by case/andP: (Hk).
move=> /= pr Hpr.
set f := [ffun _ => _].
have {f} ->:
     f = [ffun ix => arr ((pr * pl * tperm (fin_decode ix_part)
                                           (fin_decode ix_pivot) * pp)%g ix)] by
  apply/ffunP => ?; rewrite !ffunE !permM.
move=> Hsortr.
apply QuicksortRecSpec_ => [| ix ix' H H0 H1]; first by
  do !apply perm_onM; [ apply (subset_trans Hpr) | apply (subset_trans Hpl) | |
                        apply (subset_trans Hpp)];
  apply/subsetP => x; rewrite !inE; try (move: (Hk); ssromega);
  case: tpermP; rewrite ?eqxx => // -> _; rewrite fin_decodeK;
  move: (Hk); ssromega.
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
            (inj_tperm _ _ _ (@fin_encode_inj _)) !fin_decodeK permE /=
            -!(inj_eq (@ord_inj _)) /=; do !case: eqP; ssromega.
- move/ord_inj in H3; subst ix' => {H2}.
  rewrite !(out_perm Hpr, out_perm (x := _ ix_part) Hpl, tpermL,
            out_perm (x := _ ix_pivot) Hpp);
    try by rewrite inE fin_decodeK; ssromega.
  move: (perm_closed (fin_decode ix) Hpl); rewrite !inE fin_decodeK /= => H2.
  apply Hcmp_asym.
  rewrite -[X in pp X]fin_encodeK -(ffunE (fun ix => arr (pp ix))) Hpart
          (inj_tperm _ _ _ (@fin_encode_inj _)) fin_decodeK permE /=
          -!(inj_eq (@ord_inj _)) fin_decodeK; do !case: eqP; ssromega.
- move: (Hsortr ix ix'); rewrite !ffunE !permM; apply; ssromega.
- move/ord_inj in H2; subst ix => {H3}.
  move: (perm_closed (fin_decode ix') Hpr); rewrite !inE !fin_decodeK => H2.
  rewrite (out_perm Hpr) ?(out_perm Hpl) ?tpermL 1?(out_perm Hpp);
    try by rewrite ?inE ?fin_decodeK; move: (Hk); ssromega.
  rewrite -(fin_encodeK (pr _)) -(inj_tperm _ _ _ (@fin_decode_inj _))
          -(ffunE (fun ix => arr (pp ix))) tpermD ?Hpart -?(inj_eq (@ord_inj _));
    move: (Hk); ssromega.
Qed.

Variant quicksort_spec (arr : {ffun I -> A}) :
  unit * {ffun I -> A} -> Type :=
  QuicksortSpec (p : {perm I}) :
  let arr' := [ffun ix => arr (p ix)] in
  (forall ix ix' : 'I_#|I|,
    ix <= ix' -> cmp (arr' (fin_decode ix)) (arr' (fin_decode ix'))) ->
  quicksort_spec arr (tt, arr').

Lemma run_quicksort (arr : {ffun I -> A}) :
  quicksort_spec arr (run_AState quicksort arr).
Proof.
rewrite /quicksort.
set j := Ordinal _.
have ->: j = ord_max by apply/ord_inj => /=; rewrite cardT'.
by case: run_quicksort_rec => p /= Hp Hsort; constructor => *; apply: Hsort.
Qed.

Definition quicksort_ (arr : {ffun I -> A}) : {ffun I -> A} :=
  (run_AState quicksort arr).2.

End Quicksort.
End Quicksort.

Require Import extraction_ocaml.
Unset Extraction SafeImplicits.

Extraction Implicit Quicksort.partition [I].
Extraction Implicit Quicksort.quicksort_rec [I].

Extraction Inline up_search down_search Quicksort.partition Quicksort.quicksort.

Extract Type Arity AState 0.

Extraction "../../ocaml/quicksort_o0.ml" nat_eqType ordinal_finType Quicksort.

Set Extraction Flag 8175.

Extract Type Arity AState 1.

Extraction "../../ocaml/quicksort.ml" nat_eqType ordinal_finType Quicksort.
