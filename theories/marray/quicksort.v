Require Import all_ssreflect fingroup perm core ordinal_ext Wf_nat.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Search.

Variable (I : finType) (A : Type) (f : A -> bool).

Definition up_search :
  'I_#|I|.+1 -> 'I_#|I|.+1 -> AState [:: (I, A)] 'I_#|I|.+1 :=
  Fix
    (@well_founded_ordgt #|I|.+1)
    (fun _ => 'I_#|I|.+1 -> AState [:: (I, A)] 'I_#|I|.+1)
    (fun (i : 'I_#|I|.+1) rec (j : 'I_#|I|.+1) =>
       (if i < j as cij return (i < j) = cij -> _
        then fun H : i < j =>
               x <- astate_GET (ltnidx_l H);
               if f x then astate_ret i else rec (ltnidx_ls H) (leqnn i.+1) j
        else fun _ => astate_ret j)
       (erefl (i < j))).

CoInductive up_search_spec (i j : 'I_#|I|.+1) (arr : {ffun I -> A}) :
  unit * {ffun I -> A} * 'I_#|I|.+1 -> Prop :=
  | UpSearchSpec (k : 'I_#|I|.+1) :
    i <= k <= j ->
    (forall k' : 'I_#|I|, k = k' :> nat -> k < j -> f (arr (fin_decode k'))) ->
    (forall i' : 'I_#|I|, i <= i' < k -> ~~ f (arr (fin_decode i'))) ->
    up_search_spec i j arr (tt, arr, k).

Lemma run_up_search (i j : 'I_#|I|.+1) (arr : {ffun I -> A}) :
  i <= j -> up_search_spec i j arr (run_AState (up_search i j) (tt, arr)).
Proof.
rewrite /up_search /Fix; move: (well_founded_ordgt i) => Hi.
elim/Acc_ind: i / Hi (Hi) => i _ IH Hi Hij /=; rewrite -Fix_F_eq /=.
case: {2 3}(i < j) (erefl (i < j)) => H /=; first case: ifP => H0 /=.
- constructor => /= [| k' H1 H2 | i' /andP [] H1 H2]; try ssromega.
  by move: H0; congr (f (arr (fin_decode _))); apply/ord_inj.
- case: {IH Hi} (IH (ltnidx_ls H) (leqnn i.+1)
                    (Acc_inv Hi (y := ltnidx_ls H) (leqnn i.+1)) H)
    => /= k /andP [] H1 H2 H3 H4; constructor => // [| i'];
    first by rewrite H2 andbT ltnW.
  by rewrite leq_eqVlt andb_orl => /orP []; auto => /andP [] /eqP Hii' _;
    congr (~~ (f (arr (_ _)))): (negbT H0); apply/ord_inj.
- move/negbT/(conj Hij)/andP: H;
    rewrite -leqNgt -eqn_leq => /eqP/ord_inj {Hij} Hij;
    subst j; constructor; try ssromega.
Qed.

Lemma down_search_subproof i j : j < i -> i.-1 < i.
Proof. by move/ltn_predK => ->. Qed.

Definition down_search :
  'I_#|I|.+1 -> 'I_#|I|.+1 -> AState [:: (I, A)] 'I_#|I|.+1 :=
  Fix
    (@well_founded_ordlt #|I|.+1)
    (fun _ => 'I_#|I|.+1 -> AState [:: (I, A)] 'I_#|I|.+1)
    (fun (i : 'I_#|I|.+1) rec (j : 'I_#|I|.+1) =>
       (if j < i as cij return (j < i) = cij -> _
        then fun H : j < i =>
               x <- astate_GET (ltnidx_rp H);
               if f x
               then astate_ret i
               else rec (ord_pred' (i := i) (ltnm0m H))
                        (down_search_subproof H) j
        else fun _ => astate_ret j)
       (erefl (j < i))).

CoInductive down_search_spec (i j : 'I_#|I|.+1) (arr : {ffun I -> A}) :
  unit * {ffun I -> A} * 'I_#|I|.+1 -> Prop :=
  | DownSearchSpec (k : 'I_#|I|.+1):
    j <= k <= i ->
    (forall k' : 'I_#|I|, k = k'.+1 :> nat -> j < k ->
                          f (arr (fin_decode k'))) ->
    (forall i' : 'I_#|I|, k <= i' < i -> ~~ f (arr (fin_decode i'))) ->
    down_search_spec i j arr (tt, arr, k).

Lemma run_down_search (i j : 'I_#|I|.+1) (arr : {ffun I -> A}) :
  j <= i -> down_search_spec i j arr (run_AState (down_search i j) (tt, arr)).
Proof.
rewrite /down_search /Fix; move: (well_founded_ordlt i) => Hi.
elim/Acc_ind: i / Hi (Hi) => i _ IH Hi Hji /=.
rewrite -Fix_F_eq /=.
case: {2 3}(j < i) (erefl (j < i)) => H /=; first case: ifP => /= H0.
- constructor => [| k' H1 H2 |]; try ssromega.
  by move: H0; congr (f (arr (_ _))); apply/ord_inj; rewrite /= /predn' H1.
- move: {IH} (ltn_predK H)
    (let H' : ord_pred i < i := down_search_subproof H in
     IH (ord_pred i) H' (Acc_inv Hi _ H'))
    => Hi'; rewrite /= -ltnS Hi' => /(_ H) [] /= k /andP [] H1 H2 H3 H4.
  constructor => // [| i']; first by rewrite H1 (leq_trans H2) // leq_pred.
  by rewrite -Hi' ltnS (leq_eqVlt i') andb_orr => /orP [];
    auto => /andP [] _ /eqP Hii';
    congr (~~ (f (arr (_ _)))): (negbT H0); apply/ord_inj.
- move/negbT/(conj Hji)/andP: H;
    rewrite -leqNgt -eqn_leq => /eqP /ord_inj {Hji} Hji;
    subst j; constructor; ssromega.
Qed.

End Search.

Module Quicksort.
Section Quicksort.

Variable
  (I : finType) (A : Type) (cmp : A -> A -> bool)
  (Hcmp_trans : forall x y z, cmp x y -> cmp y z -> cmp x z)
  (Hcmp_asym : forall x y, ~~ cmp y x -> cmp x y).

Fixpoint partition_rec (pivot : A) (i j : 'I_#|I|.+1) (n : nat) :
  AState [:: (I, A)] 'I_#|I|.+1 :=
  i_ <- up_search (cmp pivot) i j;
  j_ <- down_search (xpredC (cmp pivot)) j i;
  match n, i_ < j_ as cij return i_ < j_ = cij -> _ with
    | n'.+1, true => fun H : i_ < j_ =>
      SWAP (ltnidx_l H) (ltnidx_rp H);;
      partition_rec pivot (ltnidx_ls H) (ord_pred' (i := j_) (ltnm0m H)) n'
    | _, _ => fun _ => astate_ret i_
  end (erefl (i_ < j_)).

Definition partition (pivot : A) (i j : 'I_#|I|.+1) (H : i <= j) :
  AState [:: (I, A)] 'I_#|I|.+1 :=
  partition_rec pivot i j (@subn' j i H).

CoInductive partition_spec
            (pivot : A) (i j : 'I_#|I|.+1) (arr : {ffun I -> A}) :
  unit * {ffun I -> A} * 'I_#|I|.+1 -> Prop :=
  PartitionSpec (p : {perm I}) (k : 'I_#|I|.+1) :
  let arr' := [ffun ix => arr (p ix)] in
  i <= k <= j ->
  perm_on [set ix | i <= fin_encode ix < j] p ->
  (forall ix : 'I_#|I|, i <= ix < k -> ~~ cmp pivot (arr' (fin_decode ix))) ->
  (forall ix : 'I_#|I|, k <= ix < j -> cmp pivot (arr' (fin_decode ix))) ->
  partition_spec pivot i j arr (tt, arr', k).

Lemma run_partition
      (pivot : A) (i j : 'I_#|I|.+1) (Hij : i <= j) (arr : {ffun I -> A}) :
  partition_spec pivot i j arr (run_AState (partition pivot Hij) (tt, arr)).
Proof.
rewrite /partition /subn'.
have {Hij}: i <= j <= j - i + i by rewrite Hij /= subnK.
have Hid_arr (arr' : {ffun I -> A}):
  arr' = [ffun ix => arr' ((1%g : {perm I}) ix)]
  by apply/ffunP => ix; rewrite ffunE permE.
move: (j - i) => n; elim: n i j arr => /= [| n IH] i j arr.
- rewrite add0n -eqn_leq => /eqP /ord_inj Hij; subst j.
  case: run_up_search => // i';
    rewrite -eqn_leq => /eqP /ord_inj Hii'; subst i' => _ _;
    case: run_down_search => // _ _ _ _.
  by rewrite {2}(Hid_arr arr); constructor; rewrite ?leqnn ?perm_on1 // => ix;
    rewrite ?ffunE permE // => /andP [] H H0; move: (leq_trans H0 H);
    rewrite ltnn.
- rewrite addSn => /andP [] H H0.
  case: run_up_search => // i_ /andP [] Hi_ Hi_' Hup Hup'.
  case: run_down_search => // j_ /andP [] Hj_ Hj_' Hdown Hdown'.
  case: {2 3}(i_ < j_) (erefl (i_ < j_));
    last by move/negbT; rewrite -leqNgt => Hji_; rewrite {2}(Hid_arr arr);
      constructor; rewrite ?(leq_trans Hj_ Hji_) ?Hi_' ?perm_on1 // => ix;
      rewrite ?ffunE permE //; auto => /andP [] H1 H2;
      move: (Hdown' ix); rewrite (leq_trans Hji_ H1) H2 negbK => ->.
  move => Hij_ /=; rewrite run_SWAP.
  have Hij_': i_.+1 < j_.
    move: Hij_; rewrite leq_eqVlt => /orP [] // /eqP Hij_.
    have H1: i_ < #|I| by rewrite Hij_ -ltnS ltn_ord.
    by move: (Hup (Ordinal H1) erefl) (Hdown (Ordinal H1) (esym Hij_));
      rewrite Hij_ Hj_' -Hij_ ltnS Hi_ => -> // /(_ erefl).
  set i' := ltnidx_l Hij_. set i'' := ltnidx_ls Hij_.
  set j' := ltnidx_rp Hij_. set j'' := ord_pred j_.
  set arr' := [ffun k => _].
  case: (IH i'' j'' arr'); first by
    apply/andP; split; rewrite -ltnS (ltn_predK Hij_) //=;
    apply (leq_trans Hj_'), (leq_trans H0); rewrite ltnS leq_add2l leqW.
  move => /= p k /andP [H1 H2] H3.
  have {arr'} ->:
       [ffun ix => arr' (p ix)] =
       [ffun ix => arr ((p * tperm (fin_decode i') (fin_decode j'))%g ix)]
    by apply/ffunP => ix; rewrite !ffunE permM.
  move => H4 H5; constructor.
  + by rewrite (leq_trans Hi_ (ltnW H1))
               (leq_trans H2 (leq_trans (leq_pred _) Hj_')).
  + apply perm_onM; first apply (subset_trans H3);
      apply/subsetP => ix; rewrite !inE;
      first by case/andP => /= /ltnW /(leq_trans Hi_) -> /= H6;
               case: (nat_of_ord j_) H6 Hj_' => //= j_'; apply ltn_trans.
    by case: tpermP; rewrite ?eq_refl // => ->;
      rewrite fin_decodeK ?Hi_ ?(leq_trans Hij_ Hj_') //=
              -1?ltnS ?(ltn_predK Hij_) ?Hj_' ?(leq_ltn_trans Hi_ Hij_).
  + move => ix /andP [] Hix Hix'; case: (ltngtP i' ix).
    * by move => Hix''; apply/H4/andP; split.
    * move => Hix''.
      rewrite ffunE permM (out_perm H3) ?inE ?fin_decodeK 1?ltnNge 1?ltnW ?Hix''
              // tpermD; try ssromega.
      by rewrite Hup' ?Hix ?Hix''.
    * move/ord_inj => Hix''; subst ix.
      by rewrite ffunE permM (out_perm H3) ?inE ?fin_decodeK ?ltnn //
                 tpermL Hdown ?(ltn_predK Hij_) //= (leq_ltn_trans Hi_ Hij_).
  + move => ix /andP [] Hix Hix'; case: (ltngtP ix j').
    * by move => Hix''; apply/H5/andP; split.
    * move => Hix''.
      rewrite ffunE permM tpermD (out_perm H3) ?inE ?fin_decodeK
              ?ltnNge ?(ltnW Hix'') ?andbF //=; try ssromega.
      by rewrite -(negbK (cmp _ _)) Hdown' //
                 (leq_trans _ Hix'') //= (ltn_predK Hij_).
    * move/ord_inj => Hix''; subst ix.
      by rewrite ffunE permM (out_perm H3) ?inE ?fin_decodeK ?ltnn ?andbF //=
                 tpermR Hup //= (leq_trans Hij_ Hj_').
Qed.

Lemma quicksort_rec_subproof (i j k : 'I_#|I|.+1) : i < j -> k.-1 < #|I|.
Proof.
by case: k => [[| k] _] //=;
   rewrite -ltnS => /leq_trans/(_ (ltn_ord j)); case: {2 3}#|I|.
Qed.

Fixpoint quicksort_rec (i j : 'I_#|I|.+1) (n : nat) :
  AState [:: (I, A)] unit :=
  match n, i.+1 < j as cij return i.+1 < j = cij -> _ with
    | n'.+1, true => fun H : i.+1 < j =>
      let i' := ltnidx_l (ltnW H) in
      let si := ltnidx_ls (ltnW H) in
      pivot <- astate_GET i';
      k <- @partition pivot si j (ltnW H);
      let pk := ord_pred k in
      let pk' := @Ordinal #|I| pk (quicksort_rec_subproof k (ltnW H)) in
      SWAP i' pk';;
      quicksort_rec i pk n';; quicksort_rec k j n'
    | _, _ => fun _ => astate_ret tt
  end (erefl (i.+1 < j)).

Definition quicksort : AState [:: (I, A)] unit :=
  quicksort_rec ord0 (@Ordinal #|I|.+1 $|I| ltac:(by rewrite cardT')) $|I|.

Lemma run_quicksort_rec (i j : 'I_#|I|.+1) (n : nat) (arr : {ffun I -> A}) :
  j <= i + n ->
  let: (_, arr', _) := run_AState (quicksort_rec i j n) (tt, arr) in
  exists2 p : {perm I},
    arr' = [ffun ix => arr (p ix)] &
    perm_on [set ix | i <= fin_encode ix < j] p /\
    (forall ix ix' : 'I_#|I|, i <= ix -> ix < ix' -> ix' < j ->
                     cmp (arr (p (fin_decode ix))) (arr (p (fin_decode ix')))).
Proof.
have Hid_arr (arr' : {ffun I -> A}):
  [ffun ix => arr' ((1%g : {perm I}) ix)] = arr'
  by apply/ffunP => ix; rewrite ffunE permE.
elim: n i j arr => [| n IH] i j arr; rewrite (addn0, addnS) => H /=;
  first by
    exists 1%g; rewrite ?Hid_arr ?perm_on1; split => // ix ix' H0 H1 H2;
    move/(leq_trans H0)/(leq_trans H)/(leq_trans H2): (ltnW H1); rewrite ltnn.
case: {2 3}(i.+1 < j) (erefl (i.+1 < j));
  last by move/negbT; rewrite -leqNgt => H0; exists 1%g;
    rewrite ?Hid_arr ?perm_on1; split => // ix ix'; rewrite -ltnS => H1 H2 H3;
    move/(leq_trans H1)/(leq_trans H0)/(leq_trans H3): H2; rewrite ltnn.
rewrite -/(is_true _) => /= H0; case: run_partition => /= ppart k' H1.
set k := Ordinal (quicksort_rec_subproof _ _).
have Hk: k' = (@Ordinal #|I|.+1 k.+1 (ltn_ord k))
  by apply/ord_inj => /=; case: (nat_of_ord k') H1.
move: k Hk H1 => k Hk; subst k' => /=; rewrite ltnS /=.
set i' := ltnidx_l _.
have ->:
  ord_pred (@Ordinal #|I|.+1 k.+1 (ltn_ord k)) =
  Ordinal (leqW (ltn_ord k)) by apply/ord_inj => /=.
set k' := Ordinal (leqW (ltn_ord k)).
set sk := @Ordinal #|I|.+1 k.+1 (ltn_ord k).
rewrite run_SWAP => H1 Hpart1 Hpart2 Hpart3.
set arr' := [ffun _ => _].
have {arr'} ->:
  arr' = [ffun ix => arr (ppart (tperm (fin_decode i') (fin_decode k) ix))]
  by apply/ffunP => ix; rewrite !ffunE.
set arr' := [ffun _ => _].
have/(IH i k' arr'): k' <= i + n
  by rewrite -ltnS; case/andP: H1 H => _; apply leq_trans.
case: (run_AState _ _) => [] [] [] arr'' _ [] pl -> {arr''} [] /= IHl1 IHl2.
have{IH} /(IH sk j [ffun ix => arr' (pl ix)]): j <= sk + n
  by apply/(leq_trans H); rewrite ltn_add2r /=; case/andP: H1.
case: (run_AState _ _) => [] [] [] arr'' _ [] pr -> {sk arr''} [] /= IHr1 IHr2.
exists (pr * pl * tperm (fin_decode i') (fin_decode k) * ppart)%g;
  first by apply/ffunP => ix; rewrite !ffunE !permM.
split => [| ixl ixr H2 H3 H4]; rewrite ?permM.
- apply perm_onM;
    last by apply/(subset_trans Hpart1)/subsetP => ix;
            rewrite !inE => /andP [] /ltnW -> ->.
  apply perm_onM;
    last by apply/subsetP => ix; rewrite !inE; case: tpermP;
            rewrite ?eq_refl // => -> {ix} _; rewrite fin_decodeK //= leqnn;
            case/andP: H1; apply/leq_ltn_trans.
  apply perm_onM; [ apply/(subset_trans IHr1) | apply/(subset_trans IHl1) ];
    apply/subsetP => ix; rewrite !inE => /andP [].
  + by case/andP: H1 => H1 _ /ltnW/(leq_trans H1) -> ->.
  + by move => -> H2; case/andP: H1 => _; move: H2; apply ltn_trans.
- case: (ltnP k ixl) => H5;
    first by move: (IHr2 ixl ixr H5 H3 H4); rewrite !ffunE.
  rewrite (out_perm IHr1) ?inE ?fin_decodeK 1?ltnNge ?H5 //.
  case: (ltnP ixr k) => [H6 |];
    first by rewrite (out_perm IHr1) ?inE ?fin_decodeK 1?ltnNge ?(ltnW H6) //;
      move: (IHl2 ixl ixr H2 H3 H6); rewrite !ffunE.
  rewrite leq_eqVlt; case/orP => [/eqP /ord_inj |] H6.
  + subst ixr => {H5}.
    rewrite (out_perm IHr1) ?(out_perm (x := fin_decode k) IHl1) ?tpermR
            ?(out_perm (x := fin_decode i') Hpart1) ?inE ?fin_decodeK ?ltnn
            ?andbF //; apply Hcmp_asym.
    move: (Hpart2 (fin_encode (tperm (fin_decode i') (fin_decode k)
                                     (pl (fin_decode ixl))))).
    rewrite ltnS ffunE fin_encodeK; apply.
    have: fin_decode ixl \in [set ix | i <= fin_encode ix < k]
      by rewrite inE fin_decodeK H2.
    rewrite // -(perm_closed _ IHl1) (_ : i = i' :> nat) // inE leq_eqVlt =>
      /andP [] /orP [/eqP /ord_inj -> | H5 H6];
      first by rewrite fin_encodeK tpermL fin_decodeK leqnn => ->.
    by rewrite tpermD ?H5 ?(ltnW H6) //=
               (can2_eq (@fin_decodeK _) (@fin_encodeK _))
               -(inj_eq (@ord_inj _)) neq_ltn (H5, H6) // orbT.
  + have: fin_decode ixr \in [set ix | k < fin_encode ix < j]
      by rewrite inE fin_decodeK H6 H4.
    rewrite -(perm_closed _ IHr1) => Hixr.
    rewrite (out_perm (x := pr (fin_decode ixr)) IHl1); last by
      move: Hixr; rewrite !inE negb_and -leqNgt => /andP[] /ltnW ->; rewrite orbT.
    rewrite (tpermD (z := pr _)); try by
      move: Hixr; rewrite inE => /andP [Hixr Hixr'];
      rewrite (can2_eq (@fin_decodeK _) (@fin_encodeK _)) -(inj_eq (@ord_inj _))
              /= neq_ltn ?Hixr // (leq_ltn_trans (leq_trans H2 H5) Hixr).
    rewrite -(fin_encodeK (pr _)); move: Hixr; rewrite !inE;
      move: {ixr H3 H4 H6} (fin_encode _) => ixr Hixr.
    have: fin_decode ixl \in [set ix | i <= fin_encode ix <= k]
      by rewrite inE fin_decodeK H2 H5.
    rewrite -(perm_closed (s := pl) (fin_decode ixl)) => [Hixl |];
      last by apply/(subset_trans IHl1)/subsetP => ix;
              rewrite !inE => /andP [] -> /ltnW.
    rewrite -(fin_encodeK (tperm _ _ _)).
    set ixl' := fin_encode (tperm _ _ _).
    have: i <= ixl' <= k by
      move: Hixl; rewrite /ixl' inE;
      case: tpermP => //= /(f_equal (fun i => nat_of_ord (@fin_encode _ i)));
      rewrite !fin_decodeK /= => <-; rewrite !leqnn !andbT //=.
    move: {ixl H2 H5 Hixl} (Hpart3 _ Hixr) ixl'; rewrite ffunE => Hcmpr ixl;
    rewrite leq_eqVlt -(ltnS ixl k) andb_orl (_ : i = i' :> nat) //
        => /orP [/andP [/eqP /ord_inj <- _ {ixl}] | /Hpart2]; first by
      rewrite (out_perm Hpart1) ?inE ?fin_decodeK ?negb_and -?leqNgt ?leqnn.
    by rewrite ffunE => /Hcmp_asym Hcmpl; apply (Hcmp_trans Hcmpl Hcmpr).
Qed.

CoInductive quicksort_spec (arr : {ffun I -> A}) :
  unit * {ffun I -> A} * unit -> Prop :=
  QuicksortSpec (p : {perm I}) :
    (forall ix ix' : 'I_#|I|,
       ix < ix' -> cmp (arr (p (fin_decode ix))) (arr (p (fin_decode ix')))) ->
    quicksort_spec arr (tt, [ffun ix => arr (p ix)], tt).

Lemma run_quicksort (arr : {ffun I -> A}) :
  quicksort_spec arr (run_AState quicksort (tt, arr)).
Proof.
rewrite /quicksort.
set max := Ordinal _.
move: (@run_quicksort_rec ord0 max $|I| arr).
rewrite add0n leqnn => /(_ erefl).
case: (run_AState _ _) => [] [] [] arr' [] [] p -> {arr'} [] _ H.
by constructor => ix ix' Hix;
  apply H => //; subst max => /=; rewrite -cardT'.
Qed.

Definition quicksort_ (arr : {ffun I -> A}) : {ffun I -> A} :=
  (run_AState quicksort (tt, arr)).1.2.

End Quicksort.
End Quicksort.

Require Import extraction_ocaml.
Unset Extraction SafeImplicits.

Extraction Implicit Quicksort.partition_rec [I].
Extraction Implicit Quicksort.partition [I].
Extraction Implicit Quicksort.quicksort_rec [I].

Extraction Inline up_search down_search Quicksort.partition Quicksort.quicksort.

Extract Type Arity AState 0.

Extraction "../../ocaml/quicksort_o0.ml"
           nat_eqType ordinal_finType Sign runt_AState runt_AState_ Quicksort.

Set Extraction Flag 8175.

Extract Type Arity AState 1.

Extraction "../../ocaml/quicksort.ml"
           nat_eqType ordinal_finType Sign runt_AState runt_AState_ Quicksort.
