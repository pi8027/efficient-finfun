Require Import all_ssreflect all_algebra automata.
Import GRing.Theory Num.Theory.

(******************************************************************************)
(*  Presburger arithmetic                                                     *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition cons_tuple (A : Type) n (h : A) (t : A ^ n) : A ^ n.+1 :=
  [ffun m => match @split 1 n m with
               | inl _ => h
               | inr i => t i
             end].

Definition tail_tuple (A : Type) n (t : A ^ n.+1) : A ^ n :=
  [ffun m => t (rshift 1 m)].

Lemma cons_tuple_eq1 (A : Type) n (h : A) (t : A ^ n) :
  cons_tuple h t ord0 = h.
Proof. by rewrite ffunE; case: splitP. Qed.

Lemma cons_tuple_eq2 (A : Type) n (h : A) (t : A ^ n) (i : 'I_n) :
  cons_tuple h t (rshift 1 i) = t i.
Proof.
rewrite ffunE /rshift.
case: splitP => j.
- by case: j => -[].
- by rewrite /= !add1n; case=> /ord_inj <-.
Qed.

Lemma tail_tuple_eq (A : Type) n (t : A ^ n.+1) (i : 'I_n) :
  tail_tuple t i = t (rshift 1 i).
Proof. by rewrite ffunE. Qed.

Lemma cons_tuple_const (A : Type) n (x : A) :
  cons_tuple (n := n) x [ffun => x] = [ffun => x].
Proof.
apply/ffunP => /= i; rewrite !ffunE.
by case: splitP => //= i' _; rewrite ffunE.
Qed.

Lemma cons_tuple_map (A B : Type) (f : A -> B) n (h : A) (t : 'I_n -> A) :
  [ffun i => f ((cons_tuple h [ffun i => t i]) i)] =
  cons_tuple (f h) [ffun i => f (t i)].
Proof.
apply/ffunP => /= i; rewrite !ffunE.
by case: splitP => //= i' _; rewrite !ffunE.
Qed.

Lemma tail_cons_tuple (A : Type) n (h : A) (t : A ^ n) :
  tail_tuple (cons_tuple h t) = t.
Proof. by apply/ffunP => /= i; rewrite ffunE cons_tuple_eq2. Qed.

Lemma split_lshift (m n : nat) (i : 'I_m) : split (lshift n i) = inl i.
Proof.
case:splitP => /= [j /ord_inj -> // | k H].
by move: (ltn_ord i); rewrite H -{2}(addn0 m) ltn_add2l.
Qed.

Lemma split_rshift (m n : nat) (i : 'I_n) : split (rshift m i) = inr i.
Proof.
case:splitP => /= [j H | k /addnI /ord_inj -> //].
by move: (ltn_ord j); rewrite -H -{2}(addn0 m) ltn_add2l.
Qed.

Lemma max_div (T : Type) (I : seq T) f d :
  \max_(i <- I) f i %/ d = (\max_(i <- I) f i) %/ d.
Proof.
rewrite (big_endo (fun x => x %/ d)) //; last by rewrite div0n.
by move=> x y; case: (leqP x y);
  last (rewrite ltn_neqAle maxnC (maxnC (_ %/ _)) => /andP [] _);
  move=> H; rewrite (maxn_idPr H) (maxn_idPr (leq_div2r d H)).
Qed.

Lemma lez_divL d m n : (0 < d -> m <= n * d -> m %/ d <= n)%Z%R.
Proof.
by move=> H H0;
  rewrite -(ler_pmul2r H) (ler_trans _ H0) // -[X in (X <= _)%R]addr0
          {2}(divz_eq m d) ler_add2l; apply modz_ge0, lt0r_neq0.
Qed.

(* Range finType *)

Import GRing.Theory Num.Theory.

Section Range.
Variable (i k : int).

Inductive range : predArgType := Range j of (i <= j <= k)%R.

Coercion int_of_range r := let: (Range j _) := r in j.

Lemma lb_range (r : range) : (i <= r)%R. Proof. by case r => /= j /andP []. Qed.
Lemma ub_range (r : range) : (r <= k)%R. Proof. by case r => /= j /andP []. Qed.

Canonical range_subType := [subType for int_of_range].
Definition range_eqMixin := Eval hnf in [eqMixin of range by <:].
Canonical range_eqType := Eval hnf in EqType range range_eqMixin.
Definition range_choiceMixin := [choiceMixin of range by <:].
Canonical range_choiceType := Eval hnf in ChoiceType range range_choiceMixin.
Definition range_countMixin := [countMixin of range by <:].
Canonical range_countType := Eval hnf in CountType range range_countMixin.
Canonical range_subCountType := [subCountType of range].

Definition range_card := if (k - i)%R is Posz n then n.+1 else 0.

Lemma range_fin_encode_subproof j : (`|(int_of_range j - i)%R| < range_card).
Proof.
rewrite /range_card.
case: j => //= j /andP [].
rewrite -(subKr i j) ler_addl; move: (- (i - j))%R => /= {j} j'.
rewrite -(subKr (i + j')%R k) ler_addl; move: (- (i + j' - k))%R => /= k'.
rewrite -(addrA i) !(addrC i) !(addrAC _ i) !subrK.
case: j' k' => [] // j' [] //= k' _ _.
by rewrite ltnS leq_addr.
Qed.

Definition range_fin_encode (j : range) : 'I_range_card :=
  Sub `|(int_of_range j - i)%R| (range_fin_encode_subproof j).

Lemma range_fin_decode_subproof (j : 'I_range_card) : (i <= i + j <= k)%R.
Proof.
by case: j => j;
  rewrite /range_card /= ler_addl //= -ler_subr_addl; case: (k - i)%R.
Qed.

Definition range_fin_decode (j : 'I_range_card) : range :=
  Sub (i + j)%R (range_fin_decode_subproof j).

Lemma range_fin_encodeK : cancel range_fin_encode range_fin_decode.
Proof.
case=> /= j H; rewrite /range_fin_encode /range_fin_decode.
apply/val_inj => //=; case/andP: H.
rewrite -(subKr i j) ler_addl; move: (- (i - j))%R => /= {j} j'.
rewrite -(subKr (i + j')%R k) ler_addl; move: (- (i + j' - k))%R => /= k'.
by rewrite {1}(addrC i j') addrAC subrK; case: j' k' => [] // j' [].
Qed.

Lemma range_fin_decodeK : cancel range_fin_decode range_fin_encode.
Proof.
case=> j H; rewrite /range_fin_encode /range_fin_decode.
by apply/val_inj; rewrite /= {1}(addrC i j) addrAC subrK.
Qed.

Definition range_finMixin :=
  Eval hnf in BijOrdMixin range_fin_encodeK range_fin_decodeK.
Canonical range_finType := Eval hnf in FinType range range_finMixin.
Canonical range_subFinType := Eval hnf in [subFinType of range].

End Range.

(* Reachability and Reachable Sub-Automaton *)

Section reachability.

Variable (char : finType) (A : dfa char).

Definition enum_reachable p :=
  dfs (fun q => [seq dfa_trans A q c | c <- enum char]) $|A| [::] p.

Definition reachable' p q := q \in enum_reachable p.

Lemma reachable'P (p q : A) :
  reflect (exists w, q = delta p w) (reachable' p q).
Proof.
rewrite /reachable' /enum_reachable -cardT'; apply (iffP dfsP).
- case=> qs H -> {q}; elim: qs p H => //=.
  + by move=> p _; exists [::].
  + move=> q qs IH p /andP [] /mapP [] x H -> {q} /IH {IH} [xs H0].
    by exists (x :: xs).
- case=> xs -> {q}; exists (dfa_run p xs) => //=.
  elim: xs p => //= x xs IH p; rewrite IH andbT.
  by apply/mapP; exists x => //=; rewrite mem_enum.
Qed.

Lemma reachable'qq q : reachable' q q.
Proof. by apply/reachable'P; exists [::]. Qed.

Notation dfa_prune_size := (size (enum_reachable (dfa_s A))).

Definition dfa_prune_dec_table : dfa_prune_size.-tuple A :=
  Tuple (eqxx (size (enum_reachable (dfa_s A)))).

Lemma dfa_prune_enc_table_subproof q :
  reachable' (dfa_s A) q -> index q (enum_reachable (dfa_s A)) < dfa_prune_size.
Proof. by rewrite index_mem. Qed.

Definition dfa_prune_enc_table q (H : reachable' (dfa_s A) q) :
  'I_dfa_prune_size :=
  Sub (index q (enum_reachable (dfa_s A))) (dfa_prune_enc_table_subproof H).

Lemma dfa_prune_subproof q ch :
  reachable' (dfa_s A) (dfa_trans A (tnth dfa_prune_dec_table q) ch).
Proof.
have/reachable'P []: reachable' (dfa_s A) (tnth dfa_prune_dec_table q)
  by rewrite /reachable' mem_tnth.
by move=> w ->; apply/reachable'P; exists (rcons w ch);
   rewrite -cats1 delta_cat.
Qed.

Definition dfa_prune : dfa char :=
  let dfa_fin_table := [ffun q => dfa_fin A (tnth dfa_prune_dec_table q)] in
  let dfa_trans_table :=
      [ffun i => @dfa_prune_enc_table
                   (dfa_trans A (tnth dfa_prune_dec_table i.1) i.2)
                   (dfa_prune_subproof i.1 i.2)] in
  {| dfa_state      := [finType of 'I_dfa_prune_size];
     dfa_s          := @dfa_prune_enc_table (dfa_s A) (reachable'qq _);
     dfa_fin q      := dfa_fin_table q;
     dfa_trans q ch := dfa_trans_table (q, ch)
  |}.

Lemma dfa_pruneP : dfa_lang dfa_prune =i dfa_lang A.
Proof.
move=> w; rewrite !delta_accept /dfa_prune !unfold_in ffunE /=; congr dfa_fin.
suff: index (delta (dfa_s A) w) dfa_prune_dec_table =
      delta (A := dfa_prune) (dfa_prune_enc_table (reachable'qq (dfa_s A))) w
  by rewrite /tnth => <-; rewrite nth_index //; apply/reachable'P; exists w.
elim: w {2 3 6}(dfa_s A) (reachable'qq (dfa_s A)) => //= a w IH q H.
rewrite (IH (dfa_trans A q a)).
- by case/reachable'P: H => w' ->; apply/reachable'P;
     exists (rcons w' a); rewrite -cats1 delta_cat.
- move=> H0.
  rewrite delta_cons /= ffunE.
  congr (_ (delta _ _)); apply/val_inj => /=.
  congr (index (dfa_trans A _ a) _).
  by rewrite /tnth /= nth_index.
Qed.

End reachability.

(* Automata construction for Presburger arithmetic *)

Section word_assign_conversion.
Variable (fvs : nat).

Fixpoint word_of_assign' (n : nat) (assign : nat ^ fvs) : seq (bool ^ fvs) :=
  match n with
    | 0 => [::]
    | n.+1 =>
      if assign == [ffun => 0]
        then [::]
        else [ffun i => odd (assign i)] ::
             word_of_assign' n [ffun i => assign i %/ 2]
  end.

Definition word_of_assign (assign : nat ^ fvs) : seq (bool ^ fvs) :=
  word_of_assign' (\max_(i < fvs) assign i) assign.

Fixpoint assign_of_word (w : seq (bool ^ fvs)) : nat ^ fvs :=
  match w with
    | [::] => [ffun => 0]
    | ch :: w => [ffun i => ch i + assign_of_word w i * 2]
  end.

Lemma max_div2_ffunE (assign : nat ^ fvs) :
  \max_i [ffun i' => assign i' %/ 2] i = (\max_i assign i) %/ 2.
Proof. rewrite -max_div; apply eq_bigr => /= i _; apply ffunE. Qed.

Lemma woa'_eq n m (assign : nat ^ fvs) :
  \max_(i < fvs) assign i <= n -> \max_(i < fvs) assign i <= m ->
  word_of_assign' n assign = word_of_assign' m assign.
Proof.
elim: n m assign => [[| m] assign | n IH [| m] assign] //=;
  do ?case: eqP => //.
- by move=> H0 /bigmax_leqP H; case: H0;
    apply/ffunP => i; rewrite ffunE; case: (assign i) (H i erefl).
- by move=> H0 _ /bigmax_leqP H; case: H0;
    apply/ffunP => i; rewrite ffunE; case: (assign i) (H i erefl).
- by move=> _ H H0; congr cons; apply IH; rewrite max_div2_ffunE;
    [move: H | move: H0]; case: (\max_i _) => [| [| x]] //; rewrite ltnS;
    apply leq_trans; rewrite -add2n divnDl // divnn add1n ltnS leq_div.
Qed.

Lemma woa_ind (P : nat ^ fvs -> seq (bool ^ fvs) -> Prop) :
  P [ffun => 0] [::] ->
  (forall (c : bool ^ fvs) (I : nat ^ fvs) w,
    ~~((I == [ffun => 0]) && (c == [ffun => false])) ->
    P I w -> P [ffun i => c i + (I i) * 2] (c :: w)) ->
  forall I, P I (word_of_assign I).
Proof.
move=> H H0 I; rewrite /word_of_assign.
set n := (\max_(i < fvs) I i).
move: {2 3}n (leqnn n); rewrite {}/n => n; elim: n I => /=.
- move=> I /bigmax_leqP /= H1.
  have -> //: I = [ffun => 0] by
    apply/ffunP => /= i; rewrite ffunE; apply /eqP; rewrite -leqn0; apply H1.
- move=> n IH I H1; case: eqP => [-> | H2] //.
  have {1}->: I = [ffun i => [ffun i => odd (I i)] i +
                             [ffun i => I i %/ 2] i * 2] by
    apply/ffunP => /= i; rewrite !ffunE -modn2 addnC -divn_eq.
  apply H0, IH.
  + by move/eqP: H2; apply contra; case/andP => H3 H4;
      apply/eqP/ffunP => /= i; rewrite (divn_eq (I i) 2) modn2;
      move/eqP/ffunP/(_ i): H3; move/eqP/ffunP/(_ i): H4;
      rewrite !ffunE => -> ->.
  + rewrite max_div2_ffunE.
    move: H1; apply contraTT; rewrite -!ltnNge leq_divRL // => H1.
    by apply: (leq_trans _ H1); rewrite mulSn !ltnS muln2 -addnn leq_addr.
Qed.

Lemma woa_step assign :
  word_of_assign assign =
  if assign == [ffun => 0] then [::]
    else [ffun i => odd (assign i)] :: word_of_assign [ffun i => assign i %/ 2].
Proof.
rewrite /word_of_assign; case: eqP => [-> |].
- by case: (\max_(i < fvs) [ffun=> 0] i) => //= n; rewrite eqxx.
- rewrite max_div2_ffunE.
  case: {2 3 4}(\max_(i < fvs) assign i) (erefl (\max_(i < fvs) assign i)).
  + by move/eq_leq/bigmax_leqP => /= H0; case;
      apply/ffunP => i; apply/eqP; rewrite ffunE -leqn0; apply H0.
  + move=> /= n H /eqP /negbTE ->; congr cons.
    apply woa'_eq; rewrite max_div2_ffunE // H //.
    by case: n {H} => // n; rewrite -add2n divnDl // divnn add1n ltnS leq_div.
Qed.

Lemma woa0 : word_of_assign [ffun => 0] = [::].
Proof. by rewrite woa_step eqxx. Qed.

Lemma cancel_woa_aow : cancel word_of_assign assign_of_word.
Proof.
move=> I; rewrite /word_of_assign.
set n := (\max_(i < fvs) I i).
move: {2 3}n (leqnn n); rewrite {}/n => n; elim: n I => /=.
- move=> I /bigmax_leqP /= H1.
  by apply/ffunP => /= i; rewrite ffunE; apply/esym/eqP; rewrite -leqn0 H1.
- move=> n IH I H; case: eqP => [-> | _ /=] //.
  apply/ffunP => /= i; rewrite IH;
    first by rewrite !ffunE -modn2 addnC -divn_eq.
  move: H; apply contraTT.
  rewrite max_div2_ffunE -!ltnNge leq_divRL //.
  by move/(leq_trans _); apply; rewrite mulSn !addSn !ltnS leq_pmulr.
(*
Restart.
  by rewrite /cancel;
    apply (@woa_ind (fun I w => assign_of_word w = I)) => //= c I w _ <-.
*)
Qed.

Lemma cancel_aow_woa w :
  exists m, word_of_assign (assign_of_word w) ++ nseq m [ffun => false] = w.
Proof.
elim: w; first by exists 0; rewrite woa0.
move=> ch w [m H]; rewrite woa_step; case: eqP => [H0 | _].
- exists (size (ch :: w)).
  elim: {ch w H} (_ :: _) H0 => //= ch w IH H; move: IH.
  have {H} [-> -> ->] //:
    ch = [ffun => false] /\ assign_of_word w = [ffun => 0].
  by split; apply/ffunP => /= i; move/ffunP/(_ i): H; rewrite !ffunE;
    case: (ch i); case ((assign_of_word w) i).
- exists m; rewrite -{3}H /=; congr (_ :: word_of_assign _ ++ _);
    apply/ffunP => /= i; rewrite !ffunE.
  + by rewrite odd_add oddb odd_mul /= andbF addbF.
  + by rewrite addnC divnMDl // divn_small ?ltnS ?leq_b1.
Qed.

Lemma aow_cat (w1 w2 : seq (bool ^ fvs)) :
  assign_of_word (w1 ++ w2) =
  [ffun i => assign_of_word w1 i + 2 ^ size w1 * assign_of_word w2 i].
Proof.
apply/ffunP => i; rewrite ffunE; elim: w1 => //= [| ch w1 IH].
- by rewrite ffunE add0n expn0 mul1n.
- by rewrite !ffunE IH mulnDl addnA mulnAC (mulnC (_ ^ _)) expnS.
Qed.

Lemma aow_nseq0 m : assign_of_word (nseq m [ffun => false]) = [ffun => 0].
Proof. by elim: m => //= m ->; apply/ffunP => i; rewrite !ffunE. Qed.

Lemma aow_cat_nseq0 w m :
  assign_of_word (w ++ nseq m [ffun => false]) = assign_of_word w.
Proof. by apply/ffunP => /= i; rewrite aow_cat aow_nseq0 !ffunE muln0. Qed.

End word_assign_conversion.

Section dfa_of_atomic_formula.
Variable (fvs : nat) (cs : int ^ fvs) (n : int).

Definition state_lb : int := Num.min n (- \sum_(i : 'I_fvs | 0 <= cs i) cs i)%R.
Definition state_ub : int := Num.max n (- \sum_(i : 'I_fvs | cs i <= 0) cs i)%R.

Lemma afdfa_s_proof : (state_lb <= n <= state_ub)%R.
Proof. by rewrite /state_lb /state_ub ler_minl ler_maxr lerr. Qed.

Lemma afdfa_trans_proof (q : range state_lb state_ub) (ch : bool ^ fvs) :
  (state_lb <=
   ((int_of_range q - \sum_(i : 'I_fvs | ch i) cs i) %/ 2)%Z <=
   state_ub)%R.
Proof.
case: q => /= q /andP []; rewrite /state_lb /state_ub // => H H0.
by apply/andP; split;
  [case: minrP H {H0} => H H0; rewrite lez_divRL // |
   case: maxrP H0 {H} => H H0; rewrite lez_divL //];
rewrite mulz2 ler_add //; [apply (ler_trans H) | | apply: (ler_trans _ H) |];
rewrite ler_opp2 big_mkcond [X in (_ <= X)%R]big_mkcond /=;
apply ler_sum => i _; case: (ch i); case: ifP => // /negbT;
rewrite -ltrNge ltr_def => /andP [].
Qed.

Definition leq_dfa : dfa [finType of bool ^ fvs] :=
  {| dfa_state      := [finType of range state_lb state_ub];
     dfa_s          := Range afdfa_s_proof;
     dfa_fin q      := (0 <= q)%R;
     dfa_trans q ch := Range (afdfa_trans_proof q ch)
  |}.

Definition eq_dfa : dfa [finType of bool ^ fvs] :=
  {| dfa_state := [finType of option (range state_lb state_ub)];
     dfa_s     := Some (Range afdfa_s_proof);
     dfa_fin q := oapp (fun q' => 0%R == int_of_range q') false q;
     dfa_trans := fun q (ch : bool ^ fvs) =>
       oapp (fun q' =>
               if (int_of_range q' == \sum_(i : 'I_fvs | ch i) cs i %[mod 2])%Z
               then Some (Range (afdfa_trans_proof q' ch)) else None)%Z
            None q
  |}.

Lemma afdfa_step ch w :
  ((\sum_(m < fvs) cs m * (assign_of_word w) m) * 2 +
   \sum_(i < fvs | ch i) cs i)%R =
  (\sum_(m < fvs) cs m * [ffun i => (ch i + (assign_of_word w) i * 2)%N] m)%R.
Proof.
rewrite big_distrl /= (big_mkcond ch) -big_split /=; apply eq_bigr => i _.
by rewrite ffunE -mulrb -mulr_natr natz -mulrA -mulrDr addrC PoszD PoszM.
Qed.

Lemma leq_dfaP w :
  w \in dfa_lang leq_dfa = (\sum_(m < fvs) cs m * (assign_of_word w) m <= n)%R.
Proof.
rewrite delta_accept unfold_in /=.
elim: w n afdfa_s_proof => /= [| ch w IH] n' H.
- by congr Num.le; apply big_rec => // i x _ <-; rewrite ffunE mulr0.
- by rewrite {}IH lez_divRL // ler_subr_addr afdfa_step.
Qed.

Lemma eq_dfaP w :
  w \in dfa_lang eq_dfa = (\sum_(m < fvs) cs m * (assign_of_word w) m == n)%R.
Proof.
rewrite delta_accept unfold_in /=.
elim: w n afdfa_s_proof => /= [| ch w IH] n' H;
  first by congr (_ == _); apply big_rec => //= i x _ <-; rewrite ffunE mulr0.
rewrite delta_cons -afdfa_step /=; case: ifP => /=.
+ rewrite IH eqz_mod_dvd.
  have/mulrIz/inj_eq <-: (2 != 0 :> int) by [].
  rewrite !mulrzz !(mulrC (2 : int)) dvdz_eq => /eqP ->.
  by rewrite eq_sym subr_eq.
+ rewrite eqz_mod_dvd => /dvdz_mod0P H0.
  have -> /=: delta (None : eq_dfa) w = None by elim: w {IH} => //.
  rewrite eq_sym -subr_eq; apply/esym/eqP => /(f_equal (modz ^~ 2)).
  move: H0; set x := (n' - _)%R.
  case: (x %% 2)%Z (@modz_ge0 x 2 erefl) (@ltz_pmod x 2 erefl) =>
    [] [| []] //= _ _ _.
  by rewrite modzMl.
Qed.

End dfa_of_atomic_formula.

Fixpoint cons_word n a (w : seq (bool ^ n)) : seq (bool ^ n.+1) :=
  match w with
    | [::] => word_of_assign (cons_tuple a [ffun => 0])
    | ch :: w' =>
      cons_tuple (odd a) ch :: cons_word (a %/ 2) w'
  end.

Lemma cons_word_correctness n x0 w :
  cons_tuple (n := n) x0 (assign_of_word w) = assign_of_word (cons_word x0 w).
Proof.
elim: w x0 => [| ch w IH] x0; first by rewrite cancel_woa_aow.
apply/ffunP => /= i; rewrite ffunE -IH /cons_tuple !ffunE; case: splitP => i' _.
- by rewrite -modn2 addnC -divn_eq.
- by rewrite ffunE.
Qed.

Section nfa_of_exists.
Variable (fvs : nat)
         (P : nat ^ fvs.+1 -> Prop) (A : dfa [finType of bool ^ fvs.+1]).
Hypothesis (H_PA : forall w, reflect (P (assign_of_word w)) (w \in dfa_lang A)).

Definition exists_nfa_trans q ch q' :=
  [exists b : bool, dfa_trans A q (cons_tuple b ch) == q'].

Definition exists_nfa_fin q :=
  has (dfa_fin A)
      (dfs
         (fun q => [seq dfa_trans A q (cons_tuple b [ffun => false])
                    | b <- enum bool_finType])
         $|A| [::] q).

Definition nfa_of_exists : nfa [finType of bool ^ fvs] :=
  {| nfa_state := A;
     nfa_s     := dfa_s A;
     nfa_fin   := exists_nfa_fin;
     nfa_trans := exists_nfa_trans
  |}.

Lemma exists_nfa_finP q :
  reflect (exists x0 w, w \in dfa_accept A q /\
                        assign_of_word w = cons_tuple x0 [ffun => 0])
          (exists_nfa_fin q).
Proof.
rewrite /exists_nfa_fin -cardT'; apply (iffP hasP).
- move=> [q'] /dfsP [qs H ->] {q'}; elim: qs q H => /=.
  + by move=> q _ H; exists 0, [::];
      rewrite delta_accept cons_tuple_const; split.
  + move=> q' qs IH q /andP [] /mapP [] /= b _ -> {q'}
            /IH H /H {IH H} [x0] [w] [H H0].
    exists (b + x0 * 2), (cons_tuple b [ffun => false] :: w).
    split; first by [].
    apply/ffunP => /= i; rewrite ffunE H0 /cons_tuple !ffunE.
    by case: split=> // i'; rewrite !ffunE.
- move=> [x0] [w] [H H0]; exists (delta q w);
    last by move: H; rewrite delta_accept.
  apply/dfsP; exists (dfa_run q w) => //.
  elim: w q x0 H0 {H} => //= ch w IH q x0 H.
  suff: ch = cons_tuple (odd x0) [ffun => false] /\
        assign_of_word w = cons_tuple (x0 %/ 2) [ffun => 0].
    move=> [->] /IH ->.
    by rewrite andbT; apply/mapP; exists (odd x0) => //; rewrite mem_enum.
  split; apply/ffunP => /= i; move/ffunP/(_ i): H;
    rewrite /cons_tuple !ffunE; case: splitP => /= i' H.
  + by move=> <-; rewrite odd_add odd_mul /= andbF addbF oddb.
  + by rewrite !ffunE; case: (ch i).
  + by move=> <-; rewrite addnC divnMDl // divn_small ?ltnS ?leq_b1.
  + by rewrite ffunE; case: (ch i); case: ((assign_of_word w) i).
Qed.

Lemma exists_nfaP w :
  reflect (exists x0, P (cons_tuple x0 (assign_of_word w)))
          (w \in nfa_lang nfa_of_exists).
Proof.
rewrite /nfa_lang unfold_in /=; apply: (iffP idP).
- move=> H.
  suff: exists x0 m,
      cons_word x0 w ++ nseq m [ffun => false] \in dfa_accept A (dfa_s A).
    by move=> [x0] [m] /H_PA;
      rewrite aow_cat_nseq0 => H0; exists x0; rewrite cons_word_correctness.
  elim: w (dfa_s A) H =>
    [s /exists_nfa_finP [x0] [w] [H H0] |
     ch w IH s /existsP [] q /andP [] /existsP [] /= b /eqP H] /=.
  + exists x0; rewrite -{}H0.
    by case: (cancel_aow_woa w) => m H0; exists m; rewrite H0.
  + subst q => /IH [x0] [m H].
    exists (x0 * 2 + b), m.
    by rewrite dfa_accept_cons odd_add odd_mul andbF oddb divnMDl //
               divn_small ?addn0 //; case b.
- case=> x0; rewrite cons_word_correctness => /H_PA; rewrite delta_accept.
  elim: w x0 (dfa_s A) => [x0 q H0 | ch w IH x0 q] /=.
  + apply/exists_nfa_finP.
    exists x0, (word_of_assign (cons_tuple x0 [ffun=> 0])).
    by rewrite delta_accept H0 cancel_woa_aow.
  + rewrite delta_cons => /IH H0.
    apply/existsP; eexists; apply/andP; split; last exact: H0.
    by apply/existsP; exists (odd x0).
Qed.

End nfa_of_exists.

(* term and formula of Presburger arithmetic *)

Inductive term (v : nat) :=
  | t_const   of nat
  | t_var     of 'I_v
  | t_add     of term v & term v
  | t_mulc    of nat & term v.

Inductive formula (v : nat) :=
  | f_all     of formula v.+1
  | f_exists  of formula v.+1
  | f_neg     of formula v
  | f_and     of formula v & formula v
  | f_or      of formula v & formula v
  | f_imply   of formula v & formula v
  | f_leq     of term v & term v
  | f_lt      of term v & term v
  | f_eq      of term v & term v.

Fixpoint t_rename v v' (f : 'I_v -> 'I_v') (t : term v) : term v' :=
  match t with
    | t_const n => t_const v' n
    | t_var var => t_var (f var)
    | t_add t1 t2 => t_add (t_rename f t1) (t_rename f t2)
    | t_mulc n t => t_mulc n (t_rename f t)
  end.

Definition f_divisible v (n : nat) (t : term v) : formula v :=
  f_exists (@f_eq (1 + v) (t_mulc n (t_var ord0)) (t_rename (@rshift 1 _) t)).

Check (@f_all 0 (f_all (f_leq (t_var (inord 1))
                              (t_add (t_var (inord 1)) (t_var (inord 0)))))).

(* normal form of Prethburger formula *)

Inductive nformula (v : nat) :=
  | nf_exists of nformula v.+1
  | nf_neg    of nformula v
  | nf_and    of nformula v & nformula v
  | nf_or     of nformula v & nformula v
  | nf_leq    of int ^ v & int
  | nf_eq     of int ^ v & int.

(* interpretation of Presburger arithmetic  *)

Fixpoint interpret_term fvs (t : term fvs) (assign : nat ^ fvs) : nat :=
  match t with
    | t_const n => n
    | t_var v => assign v
    | t_add t t' => interpret_term t assign + interpret_term t' assign
    | t_mulc n t => n * interpret_term t assign
  end.

Fixpoint interpret_formula fvs (f : formula fvs) : nat ^ fvs -> Prop :=
  match f with
    | f_all f =>
      fun assign => forall n : nat, interpret_formula f (cons_tuple n assign)
    | f_exists f =>
      fun assign => exists n : nat, interpret_formula f (cons_tuple n assign)
    | f_neg f => fun assign => ~ interpret_formula f assign
    | f_and f f' =>
      fun assign => interpret_formula f assign /\ interpret_formula f' assign
    | f_or f f' =>
      fun assign => interpret_formula f assign \/ interpret_formula f' assign
    | f_imply f f' =>
      fun assign => interpret_formula f assign -> interpret_formula f' assign
    | f_leq t t' =>
      fun assign => interpret_term t assign <= interpret_term t' assign
    | f_lt t t' =>
      fun assign => interpret_term t assign < interpret_term t' assign
    | f_eq t t' =>
      fun assign => interpret_term t assign == interpret_term t' assign
  end.

Fixpoint interpret_nformula fvs (f : nformula fvs) : nat ^ fvs -> Prop :=
  match f with
    | nf_exists f =>
      fun assign => exists n : nat, interpret_nformula f (cons_tuple n assign)
    | nf_neg f => fun assign => ~ interpret_nformula f assign
    | nf_and f f' =>
      fun assign => interpret_nformula f assign /\ interpret_nformula f' assign
    | nf_or f f' =>
      fun assign => interpret_nformula f assign \/ interpret_nformula f' assign
    | nf_leq t n => fun assign => (\sum_(m < fvs) t m * assign m <= n)%R
    | nf_eq t n  => fun assign => (\sum_(m < fvs) t m * assign m == n)%R
  end.

(* normal form computation *)

Fixpoint normal_t fvs (t : term fvs) : int ^ fvs * int :=
  (* a_1 x_1 + ... + a_n x_n + m *)
  match t with
    | t_const n => ([ffun => 0%R], (n : int))
    | t_var v => ([ffun v' => (v == v' : int)], 0%R)
    | t_add t t' =>
      let: (cs, n) := normal_t t in
      let: (cs', m) := normal_t t' in
      ([ffun var => cs var + cs' var], n + m)%R
    | t_mulc c t =>
      let: (cs, n) := normal_t t in ([ffun var => cs var *+ c], n *+ c)%R
  end.

Fixpoint normal_f fvs (f : formula fvs) : nformula fvs :=
  match f with
    | f_all f => nf_neg (nf_exists (nf_neg (normal_f f)))
    | f_exists f => nf_exists (normal_f f)
    | f_neg f => nf_neg (normal_f f)
    | f_and f f' => nf_and (normal_f f) (normal_f f')
    | f_or f f' => nf_or (normal_f f) (normal_f f')
    | f_imply f f' => nf_or (nf_neg (normal_f f)) (normal_f f')
    | f_leq t t' =>
      let: (cs, n) := normal_t t in
      let: (cs', m) := normal_t t' in
      nf_leq [ffun var => cs var - cs' var]%R (m - n)%R
    | f_lt t t' =>
      let: (cs, n) := normal_t t in
      let: (cs', m) := normal_t t' in
      nf_leq [ffun var => cs var - cs' var]%R (m - n - 1)%R
    | f_eq t t' =>
      let: (cs, n) := normal_t t in
      let: (cs', m) := normal_t t' in
      nf_eq [ffun var => cs var - cs' var]%R (m - n)%R
  end.

(* correctness proof of normal form computation *)

Lemma nt_correct fvs (t : term fvs) assign :
  interpret_term t assign =
  (let (c, n) := normal_t t in \sum_(m < fvs) c m * assign m + n)%R :> int.
Proof.
elim: t assign => [n assign | v assign || c t] /=.
- rewrite -{1}(add0r (n : int)); congr (_ + _)%R.
  by apply big_ind => [| x y <- <- | ? _] //; rewrite ffunE mul0r.
- rewrite addr0 (bigID (eq_op^~ v)) /= big_pred1_eq ffunE eqxx mul1r addrC.
  apply/eqP; rewrite -subr_eq addrN; apply/eqP;
    apply big_ind => [| x y <- <- | ? /negPf] //.
  by rewrite ffunE eq_sym => -> /=; rewrite mul0r.
- move=> t; case_eq (normal_t t) => cs n _ IHl.
  move=> t'; case_eq (normal_t t') => cs' m _ IHr i.
  rewrite PoszD IHl IHr !addrA (addrAC _ n); congr (_ + _ + _)%R.
  by rewrite -big_split /=; apply eq_big => // i' _; rewrite ffunE mulrDl.
- case_eq (normal_t t) => cs n H IH i.
  by rewrite PoszM IH mulrDr big_distrr /= -{2}natz mulr_natl;
    f_equal; apply eq_big => // i' _; rewrite ffunE -mulr_natl natz mulrA.
Qed.

Lemma nf_correct fvs (f : formula fvs) assign :
  (forall fvs (f : nformula fvs) assign,
    let P := interpret_nformula f assign in ~ ~ P -> P) ->
  (interpret_formula f assign <-> interpret_nformula (normal_f f) assign).
Proof.
have Hbigop fvs' (a : nat ^ fvs') (cs cs' : int ^ fvs') :
    (\sum_(m0 < fvs') cs' m0 * a m0 - \sum_(m0 < fvs') cs m0 * a m0)%R
  = (\sum_(m0 < fvs') [ffun var => cs' var - cs var] m0 * a m0)%R
  by rewrite (big_endo _ (@opprD _)) // -big_split /=;
    apply eq_bigr => // i _; rewrite ffunE mulrDl mulNr.
move=> dne; move: fvs f assign; refine (formula_ind _ _ _ _ _ _ _ _ _) =>
  [fvs f IH assign | fvs f IH assign | fvs f IH assign |
   fvs f IHl f' IHr assign | fvs f IHl f' IHr assign | fvs f IHl f' IHr assign |
   fvs t t' assign /= | fvs t t' assign /= | fvs t t' assign /=].
- split=> /= [H [a] | H a].
  + by apply; apply IH, H.
  + by apply IH, dne => H0; apply H; exists a.
- by split; case=> a H; exists a; apply IH.
- by split=> H H0; apply H, IH.
- by split; case=> H H0; (split; [apply IHl | apply IHr]).
- by split; (case=> H; [left; apply IHl | right; apply IHr]).
- split=> [H | /= [H /IHl /H [] | H H0]]; last by apply IHr.
  by apply dne => /Decidable.not_or [] /dne /IHl /H /IHr.
- rewrite -lez_nat !nt_correct.
  case_eq (normal_t t); case_eq (normal_t t') => /= cs n _ cs' m _.
  by rewrite -ler_subr_addr -addrA addrC -ler_subl_addr Hbigop.
- rewrite -ltz_nat !nt_correct.
  case_eq (normal_t t); case_eq (normal_t t') => /= cs n _ cs' m _.
  by rewrite ler_sub_addr lez_addr1 -ltr_subr_addr -addrA addrC -ltr_subl_addr
             Hbigop.
- have /inj_eq <- : injective Posz by move=> ? ? [].
  rewrite !nt_correct.
  case_eq (normal_t t); case_eq (normal_t t') => /= cs n _ cs' m _.
  by rewrite eq_sym -subr_eq -addrA addrC eq_sym -subr_eq Hbigop.
Qed.

(* normal form to automata conversion *)

Fixpoint dfa_of_nformula fvs (f : nformula fvs) : dfa [finType of bool ^ fvs] :=
  match f with
    | nf_exists f' => nfa_to_dfa (nfa_of_exists (dfa_of_nformula f'))
    | nf_neg f' => dfa_compl (dfa_of_nformula f')
    | nf_and f1 f2 => dfa_op andb (dfa_of_nformula f1) (dfa_of_nformula f2)
    | nf_or f1 f2 => dfa_op orb (dfa_of_nformula f1) (dfa_of_nformula f2)
    | nf_leq t n => leq_dfa t n
    | nf_eq t n => eq_dfa t n
  end.

Lemma dfa_of_nformula_correct fvs (f : nformula fvs) w :
  reflect (interpret_nformula f (assign_of_word w))
          (w \in dfa_lang (dfa_of_nformula f)).
Proof.
move: fvs f w; refine (nformula_rect _ _ _ _ _ _) =>
  [fvs f IH w | fvs f IH w | fvs f IHl f' IHr w | fvs f IHl f' IHr w |
   fvs t n w | fvs t n w] /=.
- by rewrite -nfa_to_dfa_correct; apply exists_nfaP, IH.
- by rewrite dfa_compl_correct; apply: (iffP idP) => /IH.
- by rewrite dfa_op_correct; apply: (iffP andP); case=> /IHl H /IHr H0.
- by rewrite dfa_op_correct; apply: (iffP orP); case=> [/IHl | /IHr]; tauto.
- by rewrite leq_dfaP; apply idP.
- by rewrite eq_dfaP; apply idP.
Qed.

(* decision procedures *)

Definition presburger_dec_w fvs (f : formula fvs) w :=
  w \in dfa_lang (dfa_of_nformula (normal_f f)).

Theorem presburger_dec_wP fvs (f : formula fvs) w :
  reflect (interpret_formula f (assign_of_word w)) (presburger_dec_w f w).
Proof.
have dec_dne P : decidable P -> ~ ~ P -> P by case.
rewrite /presburger_dec_w.
apply (iffP (dfa_of_nformula_correct _ _));
  apply nf_correct => fvs' f' assign' /=;
  rewrite -(cancel_woa_aow assign');
  apply dec_dne; apply (decP (dfa_of_nformula_correct _ _)).
Qed.

Definition presburger_dec fvs (f : formula fvs) assign :=
  presburger_dec_w f (word_of_assign assign).

Theorem presburger_decP fvs (f : formula fvs) assign :
  reflect (interpret_formula f assign) (presburger_dec f assign).
Proof. by apply (iffP (presburger_dec_wP f _)); rewrite cancel_woa_aow. Qed.

Definition presburger_st_dec (f : formula 0) :=
  [::] \in dfa_lang (dfa_of_nformula (normal_f f)).

Theorem presburger_st_decP (f : formula 0) :
  reflect (interpret_formula f [ffun => 0]) (presburger_st_dec f).
Proof.
by move: (presburger_decP f [ffun => 0]);
   rewrite /presburger_st_dec /presburger_dec /presburger_dec_w woa0.
Qed.

Definition presburger_sat fvs (f : formula fvs) :=
  let A := dfa_of_nformula (normal_f f) in
  has (dfa_fin A) (enum_reachable (dfa_s A)).

Theorem presburger_satP fvs (f : formula fvs) :
  reflect (exists assign, interpret_formula f assign) (presburger_sat f).
Proof.
rewrite /presburger_sat.
set A := dfa_of_nformula (normal_f f).
apply (iffP hasP); case.
- move=> q /reachable'P [] /= w -> H.
  exists (assign_of_word w); apply/presburger_dec_wP.
  by rewrite /presburger_dec_w delta_accept.
- move=> assign; rewrite -(cancel_woa_aow assign) => /presburger_dec_wP H.
  exists (delta (dfa_s A) (word_of_assign assign)).
  + by apply/reachable'P; eexists.
  + by move: H; rewrite /presburger_dec_w delta_accept.
Qed.

Definition presburger_valid fvs (f : formula fvs) :=
  let A := dfa_of_nformula (normal_f f) in
  all (dfa_fin A) (enum_reachable (dfa_s A)).

Theorem presburger_validP fvs (f : formula fvs) :
  reflect (forall assign, interpret_formula f assign) (presburger_valid f).
Proof.
rewrite /presburger_valid.
set A := dfa_of_nformula (normal_f f).
apply (iffP allP) => H.
- move=> assign; apply/presburger_decP;
    rewrite /presburger_dec /presburger_dec_w delta_accept.
  by apply H; apply/reachable'P; eexists.
- move=> x /reachable'P [] /= w -> {x}.
  by move/presburger_dec_wP: (H (assign_of_word w));
    rewrite /presburger_dec_w delta_accept.
Qed.
