Require Import all_ssreflect all_algebra reflection_base mergesort.
Import Mergesort_tailrec.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Inductive Seq : Type :=
  | SeqAtom of rindex
  | SeqNil
  | SeqCat  of Seq & Seq
  | SeqRev  of Seq.

Fixpoint denote_Seq (A : Type) (f : rindex -> seq A) (xs : Seq) : seq A :=
  match xs with
    | SeqAtom xs => f xs
    | SeqNil => [::]
    | SeqCat xs ys => denote_Seq f xs ++ denote_Seq f ys
    | SeqRev xs => rev (denote_Seq f xs)
  end.

Fixpoint sort_Seq_rec (xs : Seq) (xss : seq (seq rindex)) : seq (seq rindex) :=
  match xs with
    | SeqAtom i => merge_sort_push leq_rindex false [:: i] xss
    | SeqNil => xss
    | SeqCat xs ys => sort_Seq_rec ys (sort_Seq_rec xs xss)
    | SeqRev xs => sort_Seq_rec xs xss
  end.

Definition sort_Seq (xs : Seq) : seq rindex :=
  merge_sort_pop leq_rindex false [::] (sort_Seq_rec xs [::]).

Lemma sort_Seq_perm (A : eqType) (f : rindex -> seq A) (xs : Seq) :
  perm_eq (denote_Seq f xs) (flatten (map f (sort_Seq xs))).
Proof.
move: (merge_sort_pop_perm leq_rindex false [::] (sort_Seq_rec xs [::])).
rewrite /sort_Seq cat0s => /(perm_map f) /perm_flatten /perm_eqrP ->.
rewrite -[denote_Seq _ _]cats0 (_ : [::] = flatten (map f (flatten [::]))) //.
elim: xs [::] => [i | | xs IHx ys IHy | xs IH] xss //=;
  try by rewrite -?(perm_eqrP (IHy _)); autoperm.
move: (merge_sort_push_perm leq_rindex false [:: i] xss).
by rewrite cat1s => /(perm_map f) /perm_flatten /perm_eqrP ->.
Qed.

Lemma perm_eq_simpl (A : eqType) (f : rindex -> seq A) (xs ys : Seq) :
  perm_eq (denote_Seq f xs) (denote_Seq f ys) =
  let (xs', ys') := perm_elim leq_rindex (sort_Seq xs) (sort_Seq ys) in
  perm_eq (flatten (map f xs')) (flatten (map f ys')).
Proof.
case: (perm_elim _ _ _) (perm_elim_perm leq_rindex (sort_Seq xs) (sort_Seq ys))
  => /= xs' ys' [].
rewrite (perm_eqlP (sort_Seq_perm _ _)) (perm_eqrP (sort_Seq_perm _ _)).
move => /(perm_map f) /perm_flatten /perm_eqlP ->
        /(perm_map f) /perm_flatten /perm_eqrP ->.
rewrite !map_cat !flatten_cat; autoperm.
Qed.

Ltac tag_seq tag xs :=
  lazymatch xs with
    | @nil ?A => constr:(xs)
    | ?x :: ?xs =>
      let xs' := tag_seq tag xs in constr:(tag [:: x] ++ xs')
    | rcons ?xs ?x =>
      let xs' := tag_seq tag xs in constr:(xs' ++ tag [:: x])
    | ?xs ++ ?ys =>
      let xs' := tag_seq tag xs in
      let ys' := tag_seq tag ys in
      constr:(xs' ++ ys')
    | catrev ?xs ?ys =>
      let xs' := tag_seq tag xs in
      let ys' := tag_seq tag ys in
      constr:(rev xs' ++ ys')
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
        lazymatch eqs' with context eqs'c [(unit * ?peq)%type] =>
          let eqs' := context eqs'c [peq] in
          set eqs := eqs'
        end
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
      | rev ?e' => let e'' := reify e' in constr: (SeqRev e'')
    end
  in
  let reify_eq e :=
    lazymatch e with ?peq = perm_eq ?xs ?ys =>
      let xs' := reify xs in
      let ys' := reify ys in
      constr: (peq = perm_eq (denote_Seq f xs') (denote_Seq f ys'))
    end
  in
  lazymatch E with
    | (?E' * ?e)%type =>
      let E'' := reify_eqs f E' in
      let e' := reify_eq e in
      constr: ((E'' * e')%type)
    | _ => reify_eq E
  end.

Ltac autoperm :=
  let do_autoperm A :=
    let tag := fresh "tag" in pose tag := (fun x : seq A => x);
    let f' := fresh "f" in pose f' := tt;
    let eqs := fresh "eqs" in tag_permeqs A tag eqs;
    myquate f' eqs tag (@nil A);
    unfold tag in eqs;
    lazymatch goal with
      | eqs := ?eqs' |- _ =>
        let eqs'' := reify_eqs f' eqs' in
        clear tag eqs;
        have eqs: eqs'' by repeat
          split;
          lazymatch goal with
            |- ?peq = _ => rewrite /peq -?cats1 ?catrevE; reflexivity
          end
    end;
    rewrite !perm_eq_simpl in eqs;
    repeat
      (let pe := fresh "pe" in set pe := perm_elim _ _ _ in eqs;
       native_compute in pe; subst pe);
    cbv iota beta in eqs
  in
  lazymatch goal with
    | |- context [@perm_eq ?A ?xs ?ys] => do_autoperm A
    | H : context [@perm_eq ?A ?xs ?ys] |- _ => do_autoperm A
  end.

Fixpoint enum_rindex (n : nat) :=
  if n is n'.+1
  then let rs := enum_rindex n' in
       map rindex_L rs ++ rindex_C :: map rindex_R rs
  else [::].

Goal False.
Time let x := eval vm_compute in (sort leq_rindex (enum_rindex 15)) in idtac.
Time let x := eval vm_compute in (path.sort leq_rindex (enum_rindex 15)) in idtac.
Abort.

Example ex1 (A : eqType) (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24 s25 s26 s27 s28 s29 s30 s31 s32 s33 s34 s35 s36 s37 s38 s39 s40 s41 s42 s43 s44 s45 s46 s47 s48 s49 s50 s51 s52 s53 s54 s55 s56 s57 s58 s59 s60 s61 s62 s63 s64 s65 s66 s67 s68 s69 s70 s71 s72 s73 s74 s75 s76 s77 s78 s79 s80 s81 s82 s83 s84 s85 s86 s87 s88 s89 s90 s91 s92 s93 s94 s95 s96 s97 s98 s99 s100 s101 s102 s103 s104 s105 s106 s107 s108 s109 s110 s111 s112 s113 s114 s115 s116 s117 s118 s119 s120 s121 s122 s123 s124 s125 s126 s127 s128 s129 s130 s131 s132 s133 s134 s135 s136 s137 s138 s139 s140 s141 s142 s143 s144 s145 s146 s147 s148 s149 s150 s151 s152 s153 s154 s155 s156 s157 s158 s159 s160 s161 s162 s163 s164 s165 s166 s167 s168 s169 s170 s171 s172 s173 s174 s175 s176 s177 s178 s179 s180 s181 s182 s183 s184 s185 s186 s187 s188 s189 s190 s191 s192 s193 s194 s195 s196 s197 s198 s199 s200 s201 s202 s203 s204 s205 s206 s207 s208 s209 s210 s211 s212 s213 s214 s215 s216 s217 s218 s219 s220 s221 s222 s223 s224 s225 s226 s227 s228 s229 s230 s231 s232 s233 s234 s235 s236 s237 s238 s239 s240 s241 s242 s243 s244 s245 s246 s247 s248 s249 s250 s251 s252 s253 s254 s255 s256 s257 s258 s259 s260 s261 s262 s263 s264 s265 s266 s267 s268 s269 s270 s271 s272 s273 s274 s275 s276 s277 s278 s279 s280 s281 s282 s283 s284 s285 s286 s287 s288 s289 s290 s291 s292 s293 s294 s295 s296 s297 s298 s299 s300 s301 s302 s303 s304 s305 s306 s307 s308 s309 s310 s311 s312 s313 s314 s315 s316 s317 s318 s319 s320 s321 s322 s323 s324 s325 s326 s327 s328 s329 s330 s331 s332 s333 s334 s335 s336 s337 s338 s339 s340 s341 s342 s343 s344 s345 s346 s347 s348 s349 s350 s351 s352 s353 s354 s355 s356 s357 s358 s359 s360 s361 s362 s363 s364 s365 s366 s367 s368 s369 s370 s371 s372 s373 s374 s375 s376 s377 s378 s379 s380 s381 s382 s383 s384 s385 s386 s387 s388 s389 s390 s391 s392 s393 s394 s395 s396 s397 s398 s399 s400 s401 s402 s403 s404 s405 s406 s407 s408 s409 s410 s411 s412 s413 s414 s415 s416 s417 s418 s419 s420 s421 s422 s423 s424 s425 s426 s427 s428 s429 s430 s431 s432 s433 s434 s435 s436 s437 s438 s439 s440 s441 s442 s443 s444 s445 s446 s447 s448 s449 s450 s451 s452 s453 s454 s455 s456 s457 s458 s459 s460 s461 s462 s463 s464 s465 s466 s467 s468 s469 s470 s471 s472 s473 s474 s475 s476 s477 s478 s479 s480 s481 s482 s483 s484 s485 s486 s487 s488 s489 s490 s491 s492 s493 s494 s495 s496 s497 s498 s499 s500 s501 s502 s503 s504 s505 s506 s507 s508 s509 s510 s511: seq A) :
  perm_eq (((((((((s425 ++ (s438 ++ s459)) ++ (s249 ++ s342)) ++ s230) ++ ((s0 ++ (s12 ++ s506)) ++ (s124 ++ (s180 ++ s325)))) ++ ((((s244 ++ s258) ++ s440) ++ (s104 ++ (s263 ++ s480))) ++ (((s289 ++ s509) ++ (s203 ++ s394)) ++ (s318 ++ (s505 ++ s322))))) ++ ((((s58 ++ ((s299 ++ s193) ++ s198)) ++ ((s219 ++ s166) ++ s224)) ++ ((s279 ++ s6) ++ (((s447 ++ s215) ++ s383) ++ (s357 ++ s314)))) ++ ((((s117 ++ s511) ++ ((s413 ++ s409) ++ (s294 ++ s445))) ++ (s96 ++ ((s291 ++ s464) ++ s483))) ++ (((s118 ++ (s467 ++ s369)) ++ (s450 ++ s303)) ++ (((s86 ++ s270) ++ s95) ++ (s365 ++ s150)))))) ++ ((((((s227 ++ s10) ++ s161) ++ (s76 ++ (s441 ++ s485))) ++ (((s228 ++ s127) ++ ((s408 ++ s358) ++ s328)) ++ ((s300 ++ s381) ++ s15))) ++ ((((s243 ++ s398) ++ (s310 ++ s146)) ++ ((s275 ++ s142) ++ s306)) ++ ((s320 ++ s75) ++ ((s207 ++ (s380 ++ s288)) ++ (s352 ++ s102))))) ++ ((((((s156 ++ s155) ++ (s62 ++ s250)) ++ s38) ++ ((s235 ++ s113) ++ (s461 ++ s61))) ++ ((((s262 ++ s149) ++ s98) ++ ((s439 ++ s460) ++ s353)) ++ ((s168 ++ (s293 ++ s295)) ++ (s471 ++ s400)))) ++ ((((s177 ++ s474) ++ s372) ++ (s71 ++ (s363 ++ s264))) ++ ((s465 ++ s19) ++ ((s37 ++ s327) ++ s498)))))) ++ ((((((((s290 ++ s347) ++ s245) ++ (s489 ++ s253)) ++ ((s221 ++ s255) ++ s502)) ++ (((s74 ++ s119) ++ (s55 ++ s14)) ++ ((s269 ++ s126) ++ (s463 ++ s153)))) ++ ((((s282 ++ s46) ++ s89) ++ (((s65 ++ s208) ++ (s361 ++ s60)) ++ ((s340 ++ s356) ++ (s151 ++ s452)))) ++ (((((s423 ++ s256) ++ s271) ++ s94) ++ (s31 ++ s267)) ++ (((s359 ++ s196) ++ s56) ++ (s292 ++ s436))))) ++ (((((s8 ++ s265) ++ ((s241 ++ s427) ++ s333)) ++ ((s204 ++ (s312 ++ s417)) ++ s49)) ++ ((s40 ++ ((s72 ++ s266) ++ (s48 ++ s462))) ++ (s259 ++ s7))) ++ ((((s39 ++ (s225 ++ s188)) ++ (s173 ++ s468)) ++ ((((s304 ++ s374) ++ s504) ++ s68) ++ ((s257 ++ s277) ++ (s181 ++ s386)))) ++ (((s297 ++ s13) ++ (s446 ++ s120)) ++ (((s185 ++ s214) ++ s138) ++ (s35 ++ s420)))))) ++ (((((((s178 ++ s112) ++ s284) ++ (s222 ++ s171)) ++ ((s331 ++ s455) ++ (s454 ++ s42))) ++ ((s22 ++ ((s260 ++ s187) ++ s111)) ++ ((s494 ++ s443) ++ (s33 ++ s286)))) ++ ((((s296 ++ s164) ++ (s163 ++ s143)) ++ ((s73 ++ s101) ++ s397)) ++ (((s308 ++ s79) ++ s192) ++ (s2 ++ (s486 ++ s339))))) ++ ((((s135 ++ s407) ++ (((s493 ++ s251) ++ s226) ++ ((s278 ++ s404) ++ s273))) ++ (((s160 ++ s351) ++ s482) ++ (s453 ++ s18))) ++ (((((s377 ++ s428) ++ s140) ++ (s157 ++ s23)) ++ ((s435 ++ s83) ++ (s121 ++ s367))) ++ ((((s137 ++ s426) ++ s411) ++ s103) ++ ((s206 ++ s136) ++ (s385 ++ s496)))))))) ++ (((((((s9 ++ (s371 ++ s90)) ++ (s125 ++ s130)) ++ ((s51 ++ s376) ++ ((s147 ++ (s248 ++ s345)) ++ ((s492 ++ s158) ++ s307)))) ++ ((((s393 ++ s29) ++ ((s283 ++ s422) ++ s78)) ++ ((s154 ++ s341) ++ (s508 ++ s301))) ++ (((s87 ++ s57) ++ (s110 ++ s488)) ++ (((s176 ++ s179) ++ s82) ++ s30)))) ++ (((((s36 ++ s92) ++ (s470 ++ s233)) ++ ((s415 ++ s501) ++ (s20 ++ s194))) ++ ((((s348 ++ s384) ++ s280) ++ (s298 ++ s85)) ++ ((s313 ++ s174) ++ (s338 ++ s350)))) ++ (((s395 ++ ((s416 ++ s458) ++ (s490 ++ s495))) ++ ((s141 ++ s123) ++ (s27 ++ s116))) ++ (((s321 ++ s343) ++ ((s405 ++ s402) ++ s419)) ++ ((s186 ++ s134) ++ ((s412 ++ s391) ++ s451)))))) ++ (((((((s131 ++ s167) ++ s52) ++ ((s242 ++ s66) ++ s129)) ++ ((s197 ++ s335) ++ (s217 ++ (s274 ++ s360)))) ++ (((s63 ++ s499) ++ ((s362 ++ s354) ++ s481)) ++ (((s231 ++ s64) ++ s309) ++ (s355 ++ (s421 ++ s378))))) ++ (((((s54 ++ s201) ++ (s43 ++ s200)) ++ (s32 ++ s172)) ++ (((s305 ++ s152) ++ s287) ++ (s414 ++ s349))) ++ (s25 ++ ((s285 ++ s484) ++ (s430 ++ s93))))) ++ ((((s148 ++ (s316 ++ s432)) ++ ((s91 ++ s332) ++ s24)) ++ ((((s232 ++ s216) ++ s370) ++ ((s431 ++ s469) ++ s252)) ++ ((s28 ++ s189) ++ s218))) ++ ((((s165 ++ s220) ++ s190) ++ ((s261 ++ s4) ++ s114)) ++ ((s213 ++ ((s390 ++ s346) ++ (s317 ++ s239))) ++ (s133 ++ s162)))))) ++ ((((((s329 ++ s53) ++ (((s388 ++ s209) ++ s396) ++ (s144 ++ (s373 ++ s246)))) ++ ((s11 ++ (s169 ++ s449)) ++ ((s389 ++ s1) ++ s45))) ++ ((((s182 ++ s41) ++ s80) ++ (s16 ++ s323)) ++ (((s366 ++ s159) ++ (s99 ++ s44)) ++ (s77 ++ ((s212 ++ s281) ++ s100))))) ++ (((((s132 ++ s254) ++ (s334 ++ s344)) ++ (((s115 ++ s81) ++ s364) ++ s50)) ++ ((s5 ++ (s418 ++ s403)) ++ (s145 ++ (s399 ++ s433)))) ++ (((((s70 ++ s240) ++ s175) ++ ((s503 ++ s108) ++ s437)) ++ (((s128 ++ s139) ++ (s199 ++ s475)) ++ (s122 ++ (s330 ++ s401)))) ++ (((s34 ++ s507) ++ (s211 ++ s392)) ++ ((s315 ++ ((s456 ++ s473) ++ s466)) ++ s88))))) ++ ((((((s319 ++ s510) ++ (s183 ++ s477)) ++ ((s472 ++ s238) ++ s210)) ++ (((s3 ++ s107) ++ (s237 ++ s457)) ++ ((s387 ++ s302) ++ s105))) ++ (((((s229 ++ s26) ++ s84) ++ (s497 ++ s424)) ++ (s195 ++ ((s311 ++ s410) ++ s368))) ++ ((s17 ++ (s234 ++ (s434 ++ s276))) ++ (s21 ++ ((s406 ++ s170) ++ s272))))) ++ (((((s191 ++ s202) ++ ((s442 ++ s500) ++ s429)) ++ ((s247 ++ s184) ++ (s223 ++ (s491 ++ s326)))) ++ (((s109 ++ (s205 ++ s487)) ++ (s448 ++ s268)) ++ s67)) ++ ((((s324 ++ s47) ++ s382) ++ ((s106 ++ s478) ++ ((s444 ++ s379) ++ s476))) ++ ((s59 ++ (s69 ++ s337)) ++ (((s479 ++ s336) ++ s375) ++ (s97 ++ s236)))))))))
          (((((((((s6 ++ s185) ++ s441) ++ ((s20 ++ s313) ++ (s40 ++ (s429 ++ s158)))) ++ (((s98 ++ s268) ++ (s337 ++ s297)) ++ ((s144 ++ s485) ++ s147))) ++ ((((s186 ++ s37) ++ ((s231 ++ s335) ++ s62)) ++ ((s287 ++ s48) ++ (s351 ++ s464))) ++ (((s233 ++ s77) ++ (s96 ++ s392)) ++ ((s507 ++ s239) ++ (s55 ++ s437))))) ++ ((((s92 ++ (s452 ++ s325)) ++ (s12 ++ s267)) ++ (((s113 ++ s385) ++ ((s370 ++ s308) ++ s244)) ++ ((s22 ++ s295) ++ (s285 ++ (s323 ++ s504))))) ++ ((((s435 ++ s65) ++ (((s248 ++ s410) ++ (s462 ++ s303)) ++ s225)) ++ (((s174 ++ (s199 ++ s178)) ++ (s182 ++ s217)) ++ ((s319 ++ (s344 ++ s396)) ++ s128))) ++ (((s188 ++ s421) ++ ((s300 ++ s190) ++ (s304 ++ s195))) ++ ((s84 ++ s35) ++ ((s506 ++ s263) ++ s230)))))) ++ ((((s3 ++ s384) ++ ((((s9 ++ s390) ++ s377) ++ (s373 ++ s60)) ++ ((s38 ++ s39) ++ (s508 ++ s478)))) ++ (((((s64 ++ s302) ++ s423) ++ ((s483 ++ s130) ++ s412)) ++ (((s161 ++ s115) ++ s117) ++ (s202 ++ s109))) ++ ((((s107 ++ s90) ++ s332) ++ ((s151 ++ s511) ++ (s112 ++ s457))) ++ ((s52 ++ s327) ++ (s345 ++ s306))))) ++ ((((((s279 ++ s391) ++ s355) ++ ((s316 ++ s296) ++ s475)) ++ (((s252 ++ s496) ++ s343) ++ (s450 ++ s153))) ++ (((s416 ++ s53) ++ s156) ++ ((s253 ++ s282) ++ s23))) ++ (((((s148 ++ s340) ++ s180) ++ ((s164 ++ s371) ++ s467)) ++ (((s124 ++ s246) ++ s89) ++ (s470 ++ s219))) ++ ((((s261 ++ s456) ++ s346) ++ s24) ++ ((s43 ++ s226) ++ (s283 ++ (s388 ++ s495)))))))) ++ (((((((s173 ++ s240) ++ s458) ++ (s2 ++ s310)) ++ (((s301 ++ s321) ++ s41) ++ ((s218 ++ s21) ++ s260))) ++ (((((s494 ++ s433) ++ s350) ++ (s379 ++ s489)) ++ (s118 ++ s17)) ++ (((s387 ++ s31) ++ ((s278 ++ s393) ++ s184)) ++ ((s466 ++ s165) ++ (s401 ++ s189))))) ++ ((((((s389 ++ s358) ++ (s486 ++ s491)) ++ (s455 ++ s201)) ++ ((s272 ++ s425) ++ (s163 ++ s95))) ++ ((s152 ++ (s236 ++ (s468 ++ s324))) ++ (s13 ++ (s169 ++ s75)))) ++ ((((s394 ++ s254) ++ (s311 ++ s262)) ++ (s338 ++ ((s378 ++ s417) ++ s403))) ++ ((s88 ++ s10) ++ ((s212 ++ s309) ++ (s149 ++ s461)))))) ++ (((((s4 ++ s78) ++ (s49 ++ s484)) ++ (((((s76 ++ s121) ++ (s241 ++ s453)) ++ ((s312 ++ s191) ++ s418)) ++ ((s460 ++ s150) ++ (s67 ++ s57))) ++ ((s183 ++ s315) ++ (s26 ++ s509)))) ++ ((((s82 ++ s365) ++ ((s125 ++ s177) ++ s176)) ++ ((s59 ++ (s479 ++ s451)) ++ (s386 ++ s86))) ++ (((s18 ++ s408) ++ (s108 ++ s362)) ++ ((s449 ++ s448) ++ (s284 ++ s404))))) ++ ((((s93 ++ (s104 ++ (s136 ++ (s407 ++ s330)))) ++ ((s445 ++ s473) ++ ((s488 ++ s500) ++ s446))) ++ (((s140 ++ s123) ++ (s97 ++ s213)) ++ (((s382 ++ s142) ++ s293) ++ (s439 ++ s166)))) ++ (((((s235 ++ s242) ++ s328) ++ (s179 ++ s133)) ++ (s15 ++ ((s16 ++ s414) ++ s447))) ++ (((s105 ++ (s194 ++ s364)) ++ (s499 ++ s275)) ++ ((s7 ++ s114) ++ s145))))))) ++ ((((((((s222 ++ s63) ++ s181) ++ (((s87 ++ s333) ++ s498) ++ (s420 ++ s349))) ++ ((s368 ++ s5) ++ (s203 ++ (s334 ++ s436)))) ++ (((((s103 ++ s326) ++ s380) ++ ((s137 ++ s372) ++ s336)) ++ (((s361 ++ s264) ++ s501) ++ ((s79 ++ s168) ++ s477))) ++ (((s465 ++ s27) ++ (s42 ++ s314)) ++ ((s438 ++ s307) ++ s299)))) ++ (((((s352 ++ s14) ++ s25) ++ ((s100 ++ s405) ++ s413)) ++ (((s70 ++ s426) ++ (s381 ++ s288)) ++ ((s234 ++ s271) ++ (s71 ++ s256)))) ++ (((((s227 ++ s172) ++ (s127 ++ s432)) ++ ((s187 ++ s434) ++ s482)) ++ ((s85 ++ s472) ++ (s454 ++ s487))) ++ (((s427 ++ s83) ++ (s210 ++ s369)) ++ ((s317 ++ s205) ++ (s56 ++ s160)))))) ++ ((((((s411 ++ s45) ++ (s1 ++ s280)) ++ ((s74 ++ s459) ++ s61)) ++ ((s322 ++ (s354 ++ s356)) ++ ((s228 ++ s440) ++ s383))) ++ ((((((s376 ++ s409) ++ s120) ++ (s73 ++ s277)) ++ (s29 ++ s359)) ++ ((s221 ++ s72) ++ (s171 ++ s8))) ++ ((((s492 ++ s471) ++ s469) ++ ((s223 ++ s480) ++ s290)) ++ (s50 ++ ((s132 ++ s66) ++ s398))))) ++ ((((s270 ++ s28) ++ ((s422 ++ s250) ++ (s257 ++ (s318 ++ s347)))) ++ ((s159 ++ s46) ++ (((s102 ++ s419) ++ s209) ++ (s211 ++ s94)))) ++ ((s0 ++ s374) ++ ((s444 ++ s204) ++ (s229 ++ s363)))))) ++ ((((((((s292 ++ s286) ++ s134) ++ s33) ++ (((s503 ++ s273) ++ s265) ++ s141)) ++ ((((s162 ++ s243) ++ s366) ++ ((s493 ++ s497) ++ s157)) ++ ((s341 ++ s266) ++ s91))) ++ ((((s106 ++ s69) ++ (s367 ++ s294)) ++ (((s138 ++ s415) ++ s428) ++ ((s99 ++ s395) ++ s192))) ++ (((s220 ++ s342) ++ s32) ++ (s360 ++ s276)))) ++ ((((s19 ++ s510) ++ (((s131 ++ s329) ++ s232) ++ s101)) ++ ((s34 ++ ((s289 ++ s474) ++ s167)) ++ ((s81 ++ (s200 ++ s170)) ++ (s269 ++ (s402 ++ s424))))) ++ ((((s406 ++ s175) ++ (s274 ++ s375)) ++ (s58 ++ ((s143 ++ s505) ++ s397))) ++ (((s54 ++ s110) ++ (s197 ++ s245)) ++ ((s111 ++ s237) ++ s129))))) ++ (((((s11 ++ s490) ++ (s249 ++ s30)) ++ ((s353 ++ s68) ++ (s259 ++ s476))) ++ (((s36 ++ ((s154 ++ s430) ++ s51)) ++ ((s281 ++ s208) ++ s119)) ++ (((s126 ++ (s339 ++ s481)) ++ (s247 ++ (s348 ++ s463))) ++ s47))) ++ (((((s116 ++ s255) ++ ((s216 ++ s122) ++ s196)) ++ (((s193 ++ s298) ++ s431) ++ (s320 ++ s443))) ++ (((s135 ++ s442) ++ ((s238 ++ s198) ++ s399)) ++ ((s400 ++ s214) ++ (s331 ++ s207)))) ++ ((((s215 ++ s44) ++ s206) ++ ((s80 ++ s305) ++ (s146 ++ s502))) ++ ((s155 ++ s139) ++ (((s258 ++ s224) ++ s357) ++ (s251 ++ s291))))))))).
Proof.
Time autoperm.
(* Finished transaction in 26.104 secs (25.967u,0.036s) (successful) *)

by rewrite !eqs.

Time Defined.
(* Finished transaction in 0.58 secs (0.576u,0.004s) (successful) *)

Print ex1.
