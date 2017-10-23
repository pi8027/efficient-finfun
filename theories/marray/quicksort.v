From Coq Require Import Wf_nat.
From mathcomp Require Import all_ssreflect fingroup perm.
Require Import core.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma well_founded_ordgt (n : nat) : well_founded (fun i j : 'I_n => j < i).
Proof.
move => i; elim: {3}n i (leq_addr i n) => [i | m IH i H];
  first by rewrite add0n => /(leq_trans (ltn_ord i)); rewrite ltnn.
by constructor => j H0; apply IH, (leq_trans H); rewrite addSnnS leq_add2l.
Qed.

Lemma well_founded_ordlt (n : nat) : well_founded (fun i j : 'I_n => i < j).
Proof.
move => i; elim: {3}n i (ltn_ord i) => [// |] m IH i.
by rewrite ltnS => H; constructor => j H0; apply IH, (leq_trans H0).
Qed.

Definition lshift' (m n : nat) (i : 'I_n) : 'I_(m + n) :=
  cast_ord (addnC n m) (lshift m i).

Definition rshift' (m n : nat) (i : 'I_m) : 'I_(m + n) :=
  cast_ord (addnC n m) (rshift n i).

Lemma fin_encode_inj (T : finType) : injective (@fin_encode T).
Proof. by apply/can_inj/fin_encodeK. Qed.

Lemma fin_decode_inj (T : finType) : injective (@fin_decode T).
Proof. by apply/can_inj/fin_decodeK. Qed.

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
               let i' := @Ordinal #|I| i (leq_trans H (ltn_ord j)) in
               x <- astate_GET i';
               if f x
               then astate_ret i
               else rec (@Ordinal #|I|.+1 i.+1 (leq_ltn_trans H (ltn_ord j)))
                        (leqnn i.+1) j
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
- constructor => /= [| k' H1 H2 | i' /andP [] H1 H2].
  + by rewrite leqnn ltnW.
  + by congr (f (arr (_ _))): H0; apply/ord_inj.
  + by move: (leq_trans H2 H1); rewrite ltnn.
- case: {IH Hi} (IH (Ordinal (leq_ltn_trans H (ltn_ord j))) (leqnn i.+1)
                    (Acc_inv Hi (y := Ordinal _) (leqnn i.+1)) H)
    => /= k /andP [] H1 H2 H3 H4; constructor => // [| i'];
    first by rewrite H2 andbT ltnW.
  by rewrite leq_eqVlt andb_orl => /orP []; auto => /andP [] /eqP Hii' _;
    congr (~~ (f (arr (_ _)))): (negbT H0); apply/ord_inj.
- move/negbT/(conj Hij)/andP: H;
    rewrite -leqNgt -eqn_leq => /eqP/ord_inj {Hij} Hij; subst j; constructor.
  + by rewrite leqnn.
  + by move => H; move: H (H); rewrite {1}ltnn.
  + by move => i' /andP [] H0 H1; move: (leq_ltn_trans H0 H1); rewrite ltnn.
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
               let H0 : i.-1 < i := down_search_subproof H in
               x <- astate_GET (@Ordinal #|I| i.-1 (leq_trans H0 (ltn_ord i)));
               if f x
               then astate_ret i
               else rec (@Ordinal #|I|.+1 i.-1 (ltn_trans H0 (ltn_ord i))) H0 j
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
- constructor => [| k' H1 H2 |]; first by rewrite ltnW /=.
  + by move: H0; congr (f (arr (_ _))); apply/ord_inj; rewrite /= H1.
  + by move => i' /andP [] H1 H2; move: (leq_trans H2 H1); rewrite ltnn.
- move: {IH} (ltn_predK H)
    (let H' := down_search_subproof H in
     IH (Ordinal (ltn_trans H' (ltn_ord i))) H' (Acc_inv Hi (Ordinal _) H'))
    => Hi'; rewrite /= -ltnS Hi' => /(_ H) [] /= k /andP [] H1 H2 H3 H4.
  constructor => // [| i']; first by rewrite H1 (leq_trans H2) // leq_pred.
  by rewrite -Hi' ltnS (leq_eqVlt i') andb_orr => /orP [];
    auto => /andP [] _ /eqP Hii';
    congr (~~ (f (arr (_ _)))): (negbT H0); apply/ord_inj.
- move/negbT/(conj Hji)/andP: H;
    rewrite -leqNgt -eqn_leq => /eqP /ord_inj {Hji} Hji; subst j; constructor.
  + by rewrite leqnn.
  + by move => k; rewrite ltnn.
  + by move => i' /andP [] H H0; move: (leq_ltn_trans H H0); rewrite ltnn.
Qed.

End Search.

Module Quicksort.
Section Quicksort.

Variable
  (I : finType) (A : Type) (cmp : A -> A -> bool)
  (* Hcmp_refl : forall x, cmp x x *)
  (Hcmp_trans : forall x y z, cmp x y -> cmp y z -> cmp x z)
  (* Hcmp_total : forall x y, cmp x y || cmp y x *)
  (Hcmp_asym : forall x y, ~~ cmp y x -> cmp x y).

Definition swap (i j : 'I_#|I|) : AState [:: (I, A)] unit :=
  x <- astate_GET i; y <- astate_GET j; astate_SET i y;; astate_SET j x.

Lemma run_swap (i j : 'I_#|I|) (f : {ffun I -> A}) :
  let i' := fin_decode i in
  let j' := fin_decode j in
  run_AState (swap i j) (tt, f) =
  (tt, [ffun k => if k == i' then f j' else if k == j' then f i' else f k], tt).
Proof.
congr (tt, _, tt); apply/ffunP => k;
  rewrite !ffunE; do !case: eqP => /=; congruence.
Qed.

Opaque swap.

Lemma partition_rec_subproof1 (i j : 'I_#|I|.+1) : i < j -> j.-1 < #|I|.
Proof. by case: j => -[]. Qed.

Lemma partition_rec_subproof2 (i j : 'I_#|I|.+1) : i < j -> i.+1 < #|I|.+1.
Proof. by rewrite -ltnS; move/leq_trans; apply; apply ltn_ord. Qed.

Fixpoint partition_rec (pivot : A) (i j : 'I_#|I|.+1) (n : nat) :
  AState [:: (I, A)] 'I_#|I|.+1 :=
  i_ <- up_search (cmp pivot) i j;
  j_ <- down_search (xpredC (cmp pivot)) j i;
  match n, i_ < j_ as cij return i_ < j_ = cij -> _ with
    | n'.+1, true => fun H : i_ < j_ =>
      swap (@Ordinal #|I| i_ (leq_trans H (ltn_ord j_)))
           (@Ordinal #|I| j_.-1 (partition_rec_subproof1 H));;
      partition_rec pivot
        (@Ordinal #|I|.+1 i_.+1 (partition_rec_subproof2 H))
        (@Ordinal #|I|.+1 j_.-1 (leq_ltn_trans (leq_pred j_) (ltn_ord j_))) n'
    | _, _ => fun _ => astate_ret i_
  end (erefl (i_ < j_)).

Definition partition (pivot : A) (i j : 'I_#|I|.+1) :
  AState [:: (I, A)] 'I_#|I|.+1 :=
  partition_rec pivot i j (j - i).

CoInductive partition_spec
            (pivot : A) (i j : 'I_#|I|.+1) (arr : {ffun I -> A}) :
  unit * {ffun I -> A} * 'I_#|I|.+1 -> Prop :=
  PartitionSpec (p : {perm I}) (k : 'I_#|I|.+1) :
  let arr' := [ffun ix => arr (p ix)] in
  i <= k <= j ->
  (forall ix : 'I_#|I|, (ix < i) || (j <= ix) ->
                        p (fin_decode ix) = fin_decode ix) ->
  (forall ix : 'I_#|I|, i <= ix < k -> ~~ cmp pivot (arr' (fin_decode ix))) ->
  (forall ix : 'I_#|I|, k <= ix < j -> cmp pivot (arr' (fin_decode ix))) ->
  partition_spec pivot i j arr (tt, arr', k).

Lemma run_partition (pivot : A) (i j : 'I_#|I|.+1) (arr : {ffun I -> A}) :
  i <= j ->
  partition_spec pivot i j arr (run_AState (partition pivot i j) (tt, arr)).
Proof.
rewrite /partition => H.
have {H}: i <= j <= j - i + i by rewrite H /= subnK.
have Hid_arr (arr' : {ffun I -> A}):
  arr' = [ffun ix => arr' ((1%g : {perm I}) ix)]
  by apply/ffunP => ix; rewrite ffunE permE.
move: (j - i) => n; elim: n i j arr => /= [| n IH] i j arr.
- rewrite add0n -eqn_leq => /eqP /ord_inj Hij; subst j.
  case: run_up_search => // i';
    rewrite -eqn_leq => /eqP /ord_inj Hii'; subst i' => _ _;
    case: run_down_search => // _ _ _ _.
  by rewrite {2}(Hid_arr arr); constructor; rewrite ?leqnn // => ix;
    rewrite ?ffunE permE // => /andP [] H H0; move: (leq_trans H0 H);
    rewrite ltnn.
- rewrite addSn => /andP [] H H0.
  case: run_up_search => // i_ /andP [] Hi_ Hi_' Hup Hup'.
  case: run_down_search => // j_ /andP [] Hj_ Hj_' Hdown Hdown'.
  case: {2 3}(i_ < j_) (erefl (i_ < j_));
    last by move/negbT; rewrite -leqNgt => Hji_; rewrite {2}(Hid_arr arr);
      constructor; rewrite ?(leq_trans Hj_ Hji_) ?Hi_' // => ix;
      rewrite ?ffunE permE //; auto => /andP [] H1 H2;
      move: (Hdown' ix); rewrite (leq_trans Hji_ H1) H2 negbK => ->.
  move => Hij_ /=; rewrite run_swap.
  have Hij_': i_.+1 < j_.
    move: Hij_; rewrite leq_eqVlt => /orP [] // /eqP Hij_.
    have H1: i_ < #|I| by rewrite Hij_ -ltnS ltn_ord.
    by move: (Hup (Ordinal H1) erefl) (Hdown (Ordinal H1) (esym Hij_));
      rewrite Hij_ Hj_' -Hij_ ltnS Hi_ => -> // /(_ erefl).
  set i' := @Ordinal #|I| i_ _. set j' := @Ordinal #|I| j_.-1 _.
  set i'' := @Ordinal #|I|.+1 i_.+1 _. set j'' := @Ordinal #|I|.+1 j_.-1 _.
  set arr' := [ffun k => _].
  have/(IH i'' j'' arr') [/= p k /andP [H1 H2] H3]: i'' <= j'' <= n + i''
    by subst arr' i' j' i'' j''; apply/andP; split;
       rewrite -ltnS (ltn_predK Hij_) //=;
       apply (leq_trans Hj_'), (leq_trans H0); rewrite ltnS leq_add2l leqW.
  have {arr'} ->:
       [ffun ix => arr' (p ix)] =
       [ffun ix => arr ((p * tperm (fin_decode i') (fin_decode j'))%g ix)] by
    apply/ffunP => ix; rewrite !ffunE permM; case: tpermP;
    do ?(move => -> || move/(introF eqP) => ->); rewrite ?eqxx //;
    case: ifP Hij_' => // /eqP/fin_decode_inj/(f_equal (@nat_of_ord _)) /= <-;
    rewrite (ltn_predK Hij_) ltnn.
  move => H4 H5; constructor.
  + by rewrite (leq_trans Hi_ (ltnW H1))
               (leq_trans H2 (leq_trans (leq_pred _) Hj_')).
  + move => ix Hix; rewrite permM.
    have/H3 ->: (ix < i'') || (j'' <= ix) by
      move/orP: Hix => [ /leq_trans/(_ Hi_)/leqW |
                         /(leq_trans Hj_')/(leq_trans (leq_pred _))] -> //;
      rewrite orbT.
    by rewrite tpermD ?fin_decodeK //; apply/eqP => /fin_decode_inj Hix';
       subst ix; move: Hix; apply/negP;
       rewrite negb_or -leqNgt -ltnNge /= ?Hi_ /= ?(leq_trans Hij_ Hj_') //
               -ltnS (ltn_predK Hij_) (leq_ltn_trans Hi_ Hij_).
  + move => ix /andP [] Hix Hix'; case: (ltngtP i' ix).
    * by move => Hix''; apply/H4/andP; split.
    * move => Hix''; rewrite ffunE permM tpermD H3 ?leqW //.
      - by rewrite Hup' ?Hix ?Hix''.
      - by apply/eqP => /fin_decode_inj Hix''';
           subst ix; move: Hix''; rewrite ltnn.
      - by apply/eqP => /fin_decode_inj Hix'''; subst ix; move: Hix'';
           rewrite (ltn_predK Hij_) => /(leq_trans Hij_); rewrite ltnn.
    * move/ord_inj => Hix''; subst ix.
      rewrite ffunE permM H3 ?leqnn //= tpermL Hdown ?(ltn_predK Hij_) //=.
      by apply (leq_ltn_trans Hi_ Hij_).
  + move => ix /andP [] Hix Hix'; case: (ltngtP ix j').
    * by move => Hix''; apply/H5/andP; split.
    * move => Hix''; rewrite ffunE permM tpermD H3 ?(ltnW Hix'') ?orbT //.
      - by rewrite -(negbK (cmp _ _)) Hdown' // (leq_trans _ Hix'') //=
                   (ltn_predK Hij_).
      - by apply/eqP => /fin_decode_inj Hix'''; subst ix; move: Hix'';
           rewrite (ltn_predK Hij_) => /(leq_trans Hij_); rewrite ltnn.
      - by apply/eqP => /fin_decode_inj Hix''';
           subst ix; move: Hix''; rewrite ltnn.
    * move/ord_inj => Hix''; subst ix.
      rewrite ffunE permM H3 ?leqnn ?orbT //= tpermR Hup //=.
      by apply (leq_trans Hij_ Hj_').
Qed.

Lemma quicksort_rec_subproof1 (i j : 'I_#|I|.+1) : i < j -> i < #|I|.
Proof. by move => H; rewrite (leq_trans H (ltn_ord j)). Qed.

Lemma quicksort_rec_subproof2 (i j : 'I_#|I|.+1) : i < j -> i.+1 < #|I|.+1.
Proof. by move => H; rewrite ltnS (leq_trans H (ltn_ord j)). Qed.

Lemma quicksort_rec_subproof3 ( k : 'I_#|I|.+1) : k.-1 < #|I|.+1.
Proof. by case: k => [[| k]] //= /ltnW. Qed.

Lemma quicksort_rec_subproof4 (i j k : 'I_#|I|.+1) : i < j -> k.-1 < #|I|.
Proof.
by case: k => [[| k] _] //=;
   rewrite -ltnS => /leq_trans/(_ (ltn_ord j)); case: {2 3}#|I|.
Qed.

Fixpoint quicksort_rec (i j : 'I_#|I|.+1) (n : nat) :
  AState [:: (I, A)] unit :=
  match n, i.+1 < j as cij return i.+1 < j = cij -> _ with
    | n'.+1, true => fun H : i.+1 < j =>
      let i' := @Ordinal #|I| i (quicksort_rec_subproof1 (ltnW H)) in
      let si := @Ordinal #|I|.+1 i.+1 (quicksort_rec_subproof2 (ltnW H)) in
      pivot <- astate_GET i';
      k <- partition pivot si j;
      let pk := @Ordinal #|I|.+1 k.-1 (quicksort_rec_subproof3 k) in
      let pk' := @Ordinal #|I| k.-1 (quicksort_rec_subproof4 k (ltnW H)) in
      swap i' pk';; quicksort_rec i pk n';; quicksort_rec k j n'
    | _, _ => fun _ => astate_ret tt
  end (erefl (i.+1 < j)).

End Quicksort.
