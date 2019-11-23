Require Import all_ssreflect all_algebra reflection_base mergesort.
Import Mergesort_tailrec.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Fixpoint sort_Seq_rec (xs : Seq) (xss : seq (seq Quote.index)) :
  seq (seq Quote.index) :=
  match xs with
    | SeqAtom i => merge_sort_push geq_index false [:: i] xss
    | SeqNil => xss
    | SeqCat xs ys | SeqCatrev xs ys => sort_Seq_rec ys (sort_Seq_rec xs xss)
    | SeqRev xs => sort_Seq_rec xs xss
  end.

Definition sort_Seq (xs : Seq) : seq Quote.index :=
  merge_sort_pop geq_index false [::] (sort_Seq_rec xs [::]).

Definition perm_eqs_norm :
  seq (bool * Seq * Seq) -> seq (bool * seq Quote.index * seq Quote.index) :=
  map (fun '(peq, xs, ys) =>
         let (xs', ys') := perm_elim geq_index (sort_Seq xs) (sort_Seq ys) in
         (peq, xs', ys')).

Lemma sort_Seq_perm (A : eqType) (m : Quote.varmap (seq A)) (xs : Seq) :
  perm_eq (flatten_map (Quote.varmap_find [::] ^~ m) (sort_Seq xs))
          (denote_Seq m xs).
Proof.
move: (merge_sort_pop_perm geq_index false [::] (sort_Seq_rec xs [::])).
rewrite /sort_Seq => /= /perm_flatten_map /permPl ->.
rewrite -[denote_Seq _ _]cats0
        -[X in _ ++ X]/(flatten_map (Quote.varmap_find [::] ^~ m) (flatten [::])).
elim: xs (Nil (seq _)) => [i | | xs IHx ys IHy | xs IHx ys IHy | xs IH] xss //=;
  try rewrite ?(permPl (IHy _)); autoperm.
by move: (merge_sort_push_perm geq_index false [:: i] xss)
  => /= /perm_flatten_map /permPl ->.
Qed.

Lemma perm_eqs_normE
      (A : eqType) (m : Quote.varmap (seq A)) (xs : seq (bool * Seq * Seq)) :
  denote_eqs1 m xs -> denote_eqs2 m (perm_eqs_norm xs).
Proof.
by elim: xs => [| [[b ys] zs] [| x xs] IH] //=;
  case: (perm_elim _ _ _) (perm_elim_perm geq_index (sort_Seq ys) (sort_Seq zs))
    => /= ys' zs' [];
  rewrite -(permPl (sort_Seq_perm _ _)) -(permPr (sort_Seq_perm _ _)) =>
    /perm_flatten_map /permPl -> /perm_flatten_map /permPr ->;
  rewrite !flatten_mapE !map_cat !flatten_cat perm_cat2l;
  case=> // Hl Hr; split=> //; apply: IH.
Qed.

Ltac perm_norm A tag vmap eqs :=
  lazymatch goal with
  | eqs := ?eqs' |- _ =>
    lazymatch myquote eqs' tag (@nil A) with
    | let f := varmap_find' ?default ?vmap' in @?F f =>
      let f := fresh "f" in
      set f := (fun (_ : Quote.index) => default);
      set vmap := vmap';
      let eqs'' := eval cbv beta in (F f) in
      let eqs''' := reify_eqs f eqs'' in
      clear f tag eqs;
      have/perm_eqs_normE eqs: (denote_eqs1 vmap eqs''')
        by repeat split;
                  lazymatch goal with
                  | |- ?peq = _ => rewrite /peq -?cats1; reflexivity
                  end
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
    let tag := fresh "tag" in pose tag := (fun x : seq A => x);
    let eqs := fresh "eqs" in tag_permeqs A tag eqs;
    let vmap := fresh "vmap" in perm_norm A tag vmap eqs;
    cbv [flatten_map] in eqs;
    rewrite ?cats0 /= {vmap} in eqs;
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

Fixpoint enum_rindex (n : nat) :=
  if n is n'.+1
  then let rs := enum_rindex n' in
       Quote.End_idx :: map Quote.Left_idx rs ++ map Quote.Right_idx rs
  else [::].

Goal False.
time let x := eval native_compute in (sort leq_index (enum_rindex 15)) in idtac.
time let x := eval native_compute in (path.sort leq_index (enum_rindex 15)) in idtac.
Abort.

Example ex1 (A : eqType) (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24 s25 s26 s27 s28 s29 s30 s31 s32 s33 s34 s35 s36 s37 s38 s39 s40 s41 s42 s43 s44 s45 s46 s47 s48 s49 s50 s51 s52 s53 s54 s55 s56 s57 s58 s59 s60 s61 s62 s63 s64 s65 s66 s67 s68 s69 s70 s71 s72 s73 s74 s75 s76 s77 s78 s79 s80 s81 s82 s83 s84 s85 s86 s87 s88 s89 s90 s91 s92 s93 s94 s95 s96 s97 s98 s99 s100 s101 s102 s103 s104 s105 s106 s107 s108 s109 s110 s111 s112 s113 s114 s115 s116 s117 s118 s119 s120 s121 s122 s123 s124 s125 s126 s127 s128 s129 s130 s131 s132 s133 s134 s135 s136 s137 s138 s139 s140 s141 s142 s143 s144 s145 s146 s147 s148 s149 s150 s151 s152 s153 s154 s155 s156 s157 s158 s159 s160 s161 s162 s163 s164 s165 s166 s167 s168 s169 s170 s171 s172 s173 s174 s175 s176 s177 s178 s179 s180 s181 s182 s183 s184 s185 s186 s187 s188 s189 s190 s191 s192 s193 s194 s195 s196 s197 s198 s199 s200 s201 s202 s203 s204 s205 s206 s207 s208 s209 s210 s211 s212 s213 s214 s215 s216 s217 s218 s219 s220 s221 s222 s223 s224 s225 s226 s227 s228 s229 s230 s231 s232 s233 s234 s235 s236 s237 s238 s239 s240 s241 s242 s243 s244 s245 s246 s247 s248 s249 s250 s251 s252 s253 s254 s255 s256 s257 s258 s259 s260 s261 s262 s263 s264 s265 s266 s267 s268 s269 s270 s271 s272 s273 s274 s275 s276 s277 s278 s279 s280 s281 s282 s283 s284 s285 s286 s287 s288 s289 s290 s291 s292 s293 s294 s295 s296 s297 s298 s299 s300 s301 s302 s303 s304 s305 s306 s307 s308 s309 s310 s311 s312 s313 s314 s315 s316 s317 s318 s319 s320 s321 s322 s323 s324 s325 s326 s327 s328 s329 s330 s331 s332 s333 s334 s335 s336 s337 s338 s339 s340 s341 s342 s343 s344 s345 s346 s347 s348 s349 s350 s351 s352 s353 s354 s355 s356 s357 s358 s359 s360 s361 s362 s363 s364 s365 s366 s367 s368 s369 s370 s371 s372 s373 s374 s375 s376 s377 s378 s379 s380 s381 s382 s383 s384 s385 s386 s387 s388 s389 s390 s391 s392 s393 s394 s395 s396 s397 s398 s399 s400 s401 s402 s403 s404 s405 s406 s407 s408 s409 s410 s411 s412 s413 s414 s415 s416 s417 s418 s419 s420 s421 s422 s423 s424 s425 s426 s427 s428 s429 s430 s431 s432 s433 s434 s435 s436 s437 s438 s439 s440 s441 s442 s443 s444 s445 s446 s447 s448 s449 s450 s451 s452 s453 s454 s455 s456 s457 s458 s459 s460 s461 s462 s463 s464 s465 s466 s467 s468 s469 s470 s471 s472 s473 s474 s475 s476 s477 s478 s479 s480 s481 s482 s483 s484 s485 s486 s487 s488 s489 s490 s491 s492 s493 s494 s495 s496 s497 s498 s499 s500 s501 s502 s503 s504 s505 s506 s507 s508 s509 s510 s511 s512 s513 s514 s515 s516 s517 s518 s519 s520 s521 s522 s523 s524 s525 s526 s527 s528 s529 s530 s531 s532 s533 s534 s535 s536 s537 s538 s539 s540 s541 s542 s543 s544 s545 s546 s547 s548 s549 s550 s551 s552 s553 s554 s555 s556 s557 s558 s559 s560 s561 s562 s563 s564 s565 s566 s567 s568 s569 s570 s571 s572 s573 s574 s575 s576 s577 s578 s579 s580 s581 s582 s583 s584 s585 s586 s587 s588 s589 s590 s591 s592 s593 s594 s595 s596 s597 s598 s599 s600 s601 s602 s603 s604 s605 s606 s607 s608 s609 s610 s611 s612 s613 s614 s615 s616 s617 s618 s619 s620 s621 s622 s623 s624 s625 s626 s627 s628 s629 s630 s631 s632 s633 s634 s635 s636 s637 s638 s639 s640 s641 s642 s643 s644 s645 s646 s647 s648 s649 s650 s651 s652 s653 s654 s655 s656 s657 s658 s659 s660 s661 s662 s663 s664 s665 s666 s667 s668 s669 s670 s671 s672 s673 s674 s675 s676 s677 s678 s679 s680 s681 s682 s683 s684 s685 s686 s687 s688 s689 s690 s691 s692 s693 s694 s695 s696 s697 s698 s699 s700 s701 s702 s703 s704 s705 s706 s707 s708 s709 s710 s711 s712 s713 s714 s715 s716 s717 s718 s719 s720 s721 s722 s723 s724 s725 s726 s727 s728 s729 s730 s731 s732 s733 s734 s735 s736 s737 s738 s739 s740 s741 s742 s743 s744 s745 s746 s747 s748 s749 s750 s751 s752 s753 s754 s755 s756 s757 s758 s759 s760 s761 s762 s763 s764 s765 s766 s767 s768 s769 s770 s771 s772 s773 s774 s775 s776 s777 s778 s779 s780 s781 s782 s783 s784 s785 s786 s787 s788 s789 s790 s791 s792 s793 s794 s795 s796 s797 s798 s799 s800 s801 s802 s803 s804 s805 s806 s807 s808 s809 s810 s811 s812 s813 s814 s815 s816 s817 s818 s819 s820 s821 s822 s823 s824 s825 s826 s827 s828 s829 s830 s831 s832 s833 s834 s835 s836 s837 s838 s839 s840 s841 s842 s843 s844 s845 s846 s847 s848 s849 s850 s851 s852 s853 s854 s855 s856 s857 s858 s859 s860 s861 s862 s863 s864 s865 s866 s867 s868 s869 s870 s871 s872 s873 s874 s875 s876 s877 s878 s879 s880 s881 s882 s883 s884 s885 s886 s887 s888 s889 s890 s891 s892 s893 s894 s895 s896 s897 s898 s899 s900 s901 s902 s903 s904 s905 s906 s907 s908 s909 s910 s911 s912 s913 s914 s915 s916 s917 s918 s919 s920 s921 s922 s923 s924 s925 s926 s927 s928 s929 s930 s931 s932 s933 s934 s935 s936 s937 s938 s939 s940 s941 s942 s943 s944 s945 s946 s947 s948 s949 s950 s951 s952 s953 s954 s955 s956 s957 s958 s959 s960 s961 s962 s963 s964 s965 s966 s967 s968 s969 s970 s971 s972 s973 s974 s975 s976 s977 s978 s979 s980 s981 s982 s983 s984 s985 s986 s987 s988 s989 s990 s991 s992 s993 s994 s995 s996 s997 s998 s999 s1000 s1001 s1002 s1003 s1004 s1005 s1006 s1007 s1008 s1009 s1010 s1011 s1012 s1013 s1014 s1015 s1016 s1017 s1018 s1019 s1020 s1021 s1022 s1023: seq A) :
  perm_eq ((((((((((s32 ++ s830) ++ s16) ++ (s123 ++ (s138 ++ ((s976 ++ s962) ++ s824)))) ++ (((s498 ++ s665) ++ (s183 ++ s94)) ++ ((s661 ++ s845) ++ s474))) ++ ((((s837 ++ s774) ++ (s13 ++ s320)) ++ ((s257 ++ s71) ++ (s168 ++ s399))) ++ (((s66 ++ s785) ++ (s53 ++ s392)) ++ ((s69 ++ s433) ++ s170)))) ++ (((((s272 ++ s992) ++ s787) ++ ((s107 ++ s35) ++ s83)) ++ (((s389 ++ s929) ++ s925) ++ (s518 ++ s215))) ++ (((((s966 ++ s207) ++ s374) ++ ((s726 ++ s211) ++ s997)) ++ ((s166 ++ (s921 ++ s534)) ++ (s550 ++ s465))) ++ (((s271 ++ s48) ++ ((s178 ++ s811) ++ s344)) ++ ((s977 ++ s852) ++ (s274 ++ s779)))))) ++ ((((((s128 ++ s980) ++ ((s314 ++ s716) ++ s1018)) ++ (((s454 ++ s870) ++ (s864 ++ s270)) ++ s241)) ++ (((s586 ++ (s734 ++ s654)) ++ (s334 ++ s514)) ++ (s113 ++ s294))) ++ (((((s442 ++ s398) ++ s974) ++ ((s782 ++ s672) ++ s443)) ++ (((s683 ++ s475) ++ s803) ++ ((s423 ++ s500) ++ s408))) ++ ((s212 ++ (s805 ++ s572)) ++ ((s771 ++ s967) ++ (s700 ++ s742))))) ++ (((((s181 ++ s699) ++ s762) ++ ((((s453 ++ s424) ++ s973) ++ s302) ++ s276)) ++ ((s402 ++ (s893 ++ s761)) ++ (s15 ++ (s875 ++ s149)))) ++ (((((s508 ++ s692) ++ s67) ++ (s62 ++ s155)) ++ ((s44 ++ s91) ++ (s224 ++ s287))) ++ ((((s497 ++ s238) ++ s148) ++ s143) ++ (((s386 ++ s352) ++ s422) ++ (s816 ++ s284))))))) ++ (((((((s935 ++ s192) ++ (s371 ++ s939)) ++ (((s387 ++ s335) ++ s770) ++ s114)) ++ ((s239 ++ (s663 ++ s906)) ++ (s8 ++ s134))) ++ ((((s368 ++ (s1006 ++ s680)) ++ (s226 ++ s863)) ++ ((s243 ++ s757) ++ (s427 ++ s266))) ++ ((((s116 ++ s450) ++ s718) ++ (s33 ++ s826)) ++ ((s198 ++ s305) ++ (s768 ++ s806))))) ++ (((((s912 ++ s446) ++ (s884 ++ s910)) ++ (s460 ++ s34)) ++ (((s338 ++ s232) ++ s808) ++ ((s112 ++ s965) ++ s419))) ++ (((((s80 ++ s172) ++ s132) ++ (s289 ++ s221)) ++ ((s130 ++ (s323 ++ s737)) ++ (s859 ++ s489))) ++ (((s353 ++ (s959 ++ s359)) ++ (s685 ++ s259)) ++ ((s432 ++ s303) ++ (s673 ++ s832)))))) ++ (((((s971 ++ s39) ++ ((s163 ++ (s964 ++ s403)) ++ (s877 ++ s220))) ++ (((s595 ++ s225) ++ (s1021 ++ s206)) ++ ((s46 ++ s689) ++ (s434 ++ s923)))) ++ (((s753 ++ s98) ++ ((s583 ++ s417) ++ s800)) ++ (((s229 ++ (s288 ++ s818)) ++ (s336 ++ s573)) ++ ((s598 ++ s360) ++ (s473 ++ s781))))) ++ ((((s222 ++ ((s889 ++ s430) ++ s223)) ++ (s100 ++ (s524 ++ (s535 ++ s822)))) ++ ((s60 ++ s51) ++ ((s639 ++ s630) ++ (s625 ++ s738)))) ++ (((((s567 ++ (s955 ++ s727)) ++ s558) ++ ((s614 ++ s652) ++ (s608 ++ s285))) ++ ((s326 ++ s173) ++ (s629 ++ s755))) ++ ((s150 ++ ((s234 ++ s324) ++ ((s396 ++ s690) ++ s632))) ++ ((s300 ++ (s400 ++ s710)) ++ (s156 ++ (s812 ++ s794))))))))) ++ (((((((((s995 ++ s919) ++ s947) ++ s50) ++ ((s895 ++ s86) ++ s704)) ++ (((s486 ++ (s554 ++ s1005)) ++ (s790 ++ s78)) ++ (((s975 ++ s731) ++ (s317 ++ s986)) ++ (s715 ++ s194)))) ++ ((((s346 ++ s133) ++ s89) ++ ((s763 ++ s526) ++ (s778 ++ s807))) ++ (((s45 ++ s59) ++ s920) ++ ((s297 ++ s451) ++ s76)))) ++ (((((s587 ++ s332) ++ s570) ++ (s10 ++ (s720 ++ s549))) ++ (((s70 ++ s940) ++ (s1016 ++ s92)) ++ (s95 ++ ((s650 ++ s580) ++ s463)))) ++ (((s647 ++ s153) ++ (((s340 ++ s468) ++ s367) ++ ((s658 ++ s213) ++ s972))) ++ (((s208 ++ s404) ++ (s909 ++ s281)) ++ (s144 ++ s585))))) ++ (((((s351 ++ (s948 ++ s869)) ++ (s28 ++ (s897 ++ s765))) ++ (((s804 ++ s892) ++ (s649 ++ s798)) ++ ((s719 ++ s783) ++ s525))) ++ ((((s160 ++ (s739 ++ s327)) ++ ((s504 ++ s164) ++ s355)) ++ (((s843 ++ s329) ++ (s299 ++ s469)) ++ (((s339 ++ s736) ++ s648) ++ (s584 ++ s983)))) ++ ((((s151 ++ s951) ++ (s950 ++ s607)) ++ ((s776 ++ s203) ++ s775)) ++ ((s979 ++ s394) ++ (s36 ++ s1008))))) ++ (((((s506 ++ s756) ++ (s191 ++ s767)) ++ ((s426 ++ s591) ++ (s667 ++ s20))) ++ ((((s791 ++ s304) ++ s503) ++ ((s802 ++ s466) ++ s932)) ++ ((s708 ++ s957) ++ (s102 ++ s1001)))) ++ (((s99 ++ (s801 ++ s638)) ++ (s111 ++ (((s169 ++ s315) ++ s162) ++ (s121 ++ s871)))) ++ (((s747 ++ (s839 ++ s809)) ++ s269) ++ (s141 ++ (s676 ++ (s868 ++ s834)))))))) ++ ((((((s411 ++ (s522 ++ s520)) ++ s139) ++ (((((s886 ++ s777) ++ s789) ++ (s383 ++ s531)) ++ (s322 ++ (s675 ++ s577))) ++ (s167 ++ (s406 ++ s501)))) ++ ((((s574 ++ s705) ++ (s543 ++ s772)) ++ (s438 ++ ((s1010 ++ s994) ++ s561))) ++ ((s68 ++ s343) ++ ((s662 ++ s464) ++ (s140 ++ s610))))) ++ (((((s678 ++ s101) ++ (s740 ++ s898)) ++ (((s953 ++ s547) ++ s693) ++ (s560 ++ s527))) ++ (((s43 ++ s319) ++ (s165 ++ s624)) ++ (((s916 ++ s636) ++ s937) ++ (s545 ++ s840)))) ++ ((((s820 ++ s376) ++ s551) ++ (s429 ++ s631)) ++ (((s958 ++ s26) ++ s0) ++ (s369 ++ s47))))) ++ ((((((s82 ++ s669) ++ (s282 ++ s254)) ++ ((s733 ++ s201) ++ s458)) ++ (((s263 ++ (s488 ++ s588)) ++ (s530 ++ s769)) ++ ((s397 ++ s568) ++ (s851 ++ s623)))) ++ ((((s519 ++ s431) ++ (s938 ++ s253)) ++ ((s613 ++ s184) ++ (s796 ++ s347))) ++ (((s606 ++ s815) ++ (s873 ++ s865)) ++ (s244 ++ ((s381 ++ s697) ++ s439))))) ++ (((((s854 ++ s511) ++ s265) ++ ((s601 ++ s375) ++ s952)) ++ (((s881 ++ s655) ++ s615) ++ ((s428 ++ s1) ++ s470))) ++ ((((s998 ++ s1017) ++ (s333 ++ s409)) ++ (s14 ++ (s552 ++ (s1023 ++ s1014)))) ++ (((s120 ++ s357) ++ (s879 ++ s483)) ++ (((s268 ++ s616) ++ s668) ++ (s633 ++ s370))))))))) ++ ((((((((((s84 ++ s900) ++ s599) ++ (s260 ++ s695)) ++ ((s200 ++ s744) ++ ((s664 ++ s283) ++ s495))) ++ ((((s817 ++ s823) ++ s216) ++ (s533 ++ (s721 ++ s657))) ++ (((s157 ++ s773) ++ (s176 ++ s575)) ++ (s517 ++ s131)))) ++ (((s487 ++ (s565 ++ s717)) ++ ((s264 ++ s65) ++ s764)) ++ (((s290 ++ s878) ++ (s205 ++ s836)) ++ (s174 ++ (s248 ++ (s999 ++ s499)))))) ++ (((((s137 ++ s49) ++ (s388 ++ (s462 ++ s922))) ++ ((s63 ++ (s750 ++ s821)) ++ ((s75 ++ (s996 ++ s949)) ++ (s79 ++ s493)))) ++ (((s749 ++ s943) ++ s38) ++ (((s651 ++ s643) ++ s987) ++ (s538 ++ s54)))) ++ ((((s831 ++ s77) ++ (s227 ++ s529)) ++ (s867 ++ s24)) ++ (((s56 ++ s516) ++ (s528 ++ s412)) ++ (s249 ++ (s364 ++ s437)))))) ++ (((((s6 ++ s642) ++ ((s108 ++ s954) ++ (s930 ++ s110))) ++ ((s179 ++ (s482 ++ (s569 ++ s589))) ++ ((s541 ++ s356) ++ s1015))) ++ ((((s29 ++ s956) ++ s682) ++ ((s145 ++ s119) ++ s416)) ++ ((s496 ++ s85) ++ ((s231 ++ s435) ++ ((s970 ++ s448) ++ s380))))) ++ ((((((s702 ++ s698) ++ s797) ++ ((s255 ++ s709) ++ s455)) ++ ((s741 ++ s262) ++ (s196 ++ s405))) ++ (((s557 ++ s391) ++ (s924 ++ s578)) ++ (s57 ++ (s490 ++ s96)))) ++ ((((s1007 ++ s1020) ++ s328) ++ (s252 ++ s42)) ++ ((s440 ++ (s993 ++ s671)) ++ ((s860 ++ s73) ++ s1000)))))) ++ ((((((s12 ++ (s182 ++ s325)) ++ ((s341 ++ s963) ++ ((s901 ++ s960) ++ s350))) ++ ((((s382 ++ s230) ++ s810) ++ ((s193 ++ s597) ++ s261)) ++ (s97 ++ (s707 ++ s563)))) ++ ((((s421 ++ s125) ++ ((s407 ++ s681) ++ (s189 ++ s256))) ++ (((s637 ++ s711) ++ s841) ++ (s853 ++ s902))) ++ (((((s293 ++ s414) ++ s619) ++ (s887 ++ s712)) ++ s154) ++ (s58 ++ s280)))) ++ ((((s677 ++ (s848 ++ s988)) ++ (s600 ++ s874)) ++ ((s228 ++ (s418 ++ s656)) ++ s5)) ++ ((((s931 ++ s379) ++ s292) ++ ((s602 ++ s581) ++ (s856 ++ s542))) ++ (((s722 ++ s969) ++ s537) ++ ((s345 ++ s908) ++ s674))))) ++ (((((s190 ++ s306) ++ (s27 ++ s2)) ++ ((s687 ++ ((s890 ++ s714) ++ (s894 ++ s814))) ++ s477)) ++ (((s907 ++ s88) ++ (s644 ++ s694)) ++ (((s562 ++ s982) ++ (s384 ++ s447)) ++ ((s915 ++ s1004) ++ s729)))) ++ ((((((s835 ++ s312) ++ s861) ++ (s251 ++ s829)) ++ (s187 ++ ((s413 ++ s978) ++ (s989 ++ s849)))) ++ (((s415 ++ s195) ++ ((s457 ++ s751) ++ s934)) ++ ((s793 ++ s31) ++ (s316 ++ s235)))) ++ (((s90 ++ ((s214 ++ s888) ++ s984)) ++ ((s118 ++ s961) ++ ((s604 ++ s523) ++ (s372 ++ s641)))) ++ (((s217 ++ s55) ++ (s944 ++ s472)) ++ ((s590 ++ s209) ++ (s491 ++ s313)))))))) ++ (((((((((s245 ++ s788) ++ s576) ++ ((s124 ++ s666) ++ s544)) ++ (((s410 ++ s579) ++ s1012) ++ ((s991 ++ s210) ++ s510))) ++ (((s611 ++ s52) ++ (s461 ++ s905)) ++ ((s348 ++ s626) ++ (s866 ++ s688)))) ++ ((((((s175 ++ s825) ++ s279) ++ s129) ++ ((s899 ++ s936) ++ s197)) ++ ((s273 ++ s240) ++ (s74 ++ s295))) ++ ((((s609 ++ s366) ++ s571) ++ (s247 ++ s1002)) ++ (s37 ++ (s109 ++ (s219 ++ s927)))))) ++ (((((s618 ++ s161) ++ (s536 ++ s330)) ++ (s61 ++ s185)) ++ ((((s592 ++ s828) ++ s945) ++ (s296 ++ (s730 ++ s548))) ++ ((s258 ++ s509) ++ ((s752 ++ s420) ++ (s635 ++ s760))))) ++ ((((s670 ++ s122) ++ ((s603 ++ s512) ++ s891)) ++ ((s117 ++ (s842 ++ s612)) ++ (s476 ++ s481))) ++ (((s311 ++ ((s582 ++ s827) ++ (s485 ++ s896))) ++ (s784 ++ s267)) ++ ((s505 ++ s236) ++ (s471 ++ s990)))))) ++ (((((((s378 ++ s142) ++ s361) ++ (s452 ++ s622)) ++ (((s301 ++ s883) ++ s640) ++ (s846 ++ s911))) ++ (((s885 ++ s40) ++ (s743 ++ s30)) ++ ((s342 ++ ((s627 ++ s436) ++ s882)) ++ s298))) ++ (((((s1003 ++ s539) ++ s914) ++ s23) ++ (((s679 ++ s393) ++ s766) ++ (s72 ++ s291))) ++ (((s459 ++ s904) ++ s21) ++ (s147 ++ (s660 ++ s362))))) ++ ((((((s594 ++ s135) ++ s479) ++ ((s467 ++ s286) ++ s928)) ++ ((s115 ++ s1022) ++ s425)) ++ ((s9 ++ s556) ++ (s358 ++ s204))) ++ ((((s308 ++ s833) ++ ((s507 ++ s754) ++ (s799 ++ s876))) ++ (((s277 ++ s521) ++ s1009) ++ s106)) ++ (((s981 ++ s19) ++ (s862 ++ s171)) ++ (((s946 ++ s968) ++ s441) ++ (s484 ++ s310))))))) ++ (((((((s4 ++ s728) ++ s628) ++ ((s918 ++ s25) ++ s321)) ++ (((s127 ++ s844) ++ s1013) ++ ((s275 ++ (s449 ++ s354)) ++ (s596 ++ (s735 ++ s926))))) ++ (((((s725 ++ s605) ++ s87) ++ (s653 ++ s780)) ++ (((s373 ++ s620) ++ s146) ++ (s199 ++ (s1019 ++ s555)))) ++ (((s41 ++ s365) ++ (s713 ++ s492)) ++ ((s81 ++ (s401 ++ s103)) ++ ((s363 ++ s93) ++ s855))))) ++ ((((((s480 ++ s684) ++ s22) ++ (s502 ++ s318)) ++ ((s723 ++ s795) ++ s11)) ++ ((((s152 ++ s880) ++ s634) ++ (s553 ++ s913)) ++ ((s858 ++ s126) ++ (s746 ++ s445)))) ++ (((s307 ++ (s337 ++ (s872 ++ s515))) ++ (s559 ++ s17)) ++ ((((s278 ++ s331) ++ (s903 ++ s745)) ++ ((s233 ++ s546) ++ s456)) ++ ((s759 ++ s158) ++ (((s645 ++ s691) ++ s202) ++ (s786 ++ s621))))))) ++ ((((((s349 ++ s701) ++ (s732 ++ s532)) ++ (s242 ++ s792)) ++ (((s706 ++ s696) ++ s3) ++ ((s105 ++ s309) ++ s985))) ++ (((s494 ++ s659) ++ ((s686 ++ (s748 ++ s838)) ++ (s566 ++ s593))) ++ ((s104 ++ (s218 ++ s703)) ++ (s188 ++ s186)))) ++ ((((s64 ++ s7) ++ (s444 ++ s857)) ++ (((s237 ++ ((s250 ++ s478) ++ s385)) ++ ((s847 ++ (s942 ++ s917)) ++ s246)) ++ ((s177 ++ s813) ++ s850))) ++ ((((s758 ++ s390) ++ (s136 ++ s159)) ++ (s18 ++ s1011)) ++ ((((s646 ++ s180) ++ s819) ++ (s513 ++ s395)) ++ (((s377 ++ s941) ++ s724) ++ ((s933 ++ s617) ++ (s564 ++ s540)))))))))))
          (((((((((((s420 ++ s961) ++ s474) ++ s126) ++ (s532 ++ s4)) ++ (((s42 ++ s927) ++ s508) ++ (s634 ++ s968))) ++ (((((s219 ++ s941) ++ s320) ++ (s539 ++ s775)) ++ (((s506 ++ s346) ++ s313) ++ (s588 ++ s815))) ++ (((s273 ++ s203) ++ (s317 ++ s169)) ++ ((s633 ++ (s651 ++ s898)) ++ ((s513 ++ s1012) ++ s657))))) ++ ((((s733 ++ s55) ++ (((s233 ++ s181) ++ s806) ++ (s580 ++ s284))) ++ (((s841 ++ s949) ++ (s921 ++ s698)) ++ (s266 ++ (s468 ++ s497)))) ++ ((s154 ++ ((s296 ++ s406) ++ (s548 ++ s595))) ++ ((((s550 ++ s183) ++ s568) ++ (s189 ++ (s797 ++ s437))) ++ ((s965 ++ s191) ++ ((s327 ++ s948) ++ s251)))))) ++ (((((s82 ++ (s172 ++ ((s788 ++ s435) ++ s645))) ++ ((s957 ++ s509) ++ ((s913 ++ s853) ++ s638))) ++ (((s200 ++ s616) ++ (s678 ++ s753)) ++ (s78 ++ s687))) ++ ((((s635 ++ s433) ++ (s92 ++ s848)) ++ (((s263 ++ s161) ++ s664) ++ s107)) ++ (((s65 ++ s660) ++ (s410 ++ s831)) ++ ((s785 ++ s422) ++ (s288 ++ s485))))) ++ (((((s135 ++ (s193 ++ s856)) ++ (s650 ++ s381)) ++ (((s947 ++ s338) ++ s934) ++ s194)) ++ (((s939 ++ s796) ++ (s385 ++ s597)) ++ ((s44 ++ s1003) ++ (s103 ++ s89)))) ++ ((((s321 ++ s452) ++ (s117 ++ s464)) ++ ((s129 ++ s484) ++ (s558 ++ s106))) ++ (((s728 ++ s504) ++ s729) ++ ((s389 ++ s35) ++ s184)))))) ++ ((((((s412 ++ (s813 ++ s793)) ++ ((s861 ++ s100) ++ s755)) ++ (((s686 ++ s769) ++ s540) ++ ((s970 ++ s14) ++ s353))) ++ ((((s579 ++ s706) ++ (s722 ++ s294)) ++ ((s582 ++ s33) ++ s598)) ++ (((s190 ++ (s396 ++ s846)) ++ (s798 ++ s344)) ++ ((s887 ++ s155) ++ (s211 ++ (s997 ++ s382)))))) ++ (((((s0 ++ s673) ++ s398) ++ (s747 ++ s754)) ++ (s23 ++ ((s408 ++ s356) ++ (s779 ++ s442)))) ++ (((s15 ++ (s599 ++ s375)) ++ (s518 ++ s688)) ++ ((((s471 ++ s589) ++ s108) ++ s64) ++ ((s39 ++ s188) ++ (s931 ++ s744)))))) ++ (((((((s293 ++ s818) ++ s228) ++ (s114 ++ s928)) ++ ((s76 ++ s869) ++ s450)) ++ ((((s262 ++ s467) ++ s726) ++ (s366 ++ (s529 ++ s523))) ++ ((s178 ++ s446) ++ s871))) ++ ((((s976 ++ s891) ++ (s640 ++ s36)) ++ (s150 ++ (s915 ++ s694))) ++ (((s208 ++ (s977 ++ s281)) ++ (s910 ++ s482)) ++ ((s473 ++ s101) ++ s674)))) ++ ((((s63 ++ (s985 ++ s67)) ++ ((s416 ++ s345) ++ (s936 ++ s441))) ++ ((s358 ++ (s563 ++ (s642 ++ s720))) ++ ((s57 ++ s1007) ++ s110))) ++ ((((s160 ++ (s875 ++ s312)) ++ (s507 ++ s974)) ++ (s165 ++ ((s311 ++ s989) ++ ((s919 ++ s457) ++ (s380 ++ s603))))) ++ (((s771 ++ s116) ++ s662) ++ (s644 ++ s122))))))) ++ ((((((((s917 ++ s614) ++ (s671 ++ s992)) ++ (s18 ++ (s610 ++ s372))) ++ ((((s96 ++ s637) ++ s249) ++ (s217 ++ s60)) ++ (((s980 ++ s763) ++ s309) ++ (s746 ++ s205)))) ++ (((((s307 ++ s88) ++ s415) ++ (s718 ++ s560)) ++ ((s918 ++ s243) ++ (s176 ++ s287))) ++ (((s397 ++ s751) ++ ((s899 ++ s950) ++ s547)) ++ (((s572 ++ s925) ++ s405) ++ s198)))) ++ (((((s162 ++ s41) ++ s756) ++ (((s979 ++ s427) ++ s944) ++ (s860 ++ s703))) ++ (((s302 ++ s701) ++ (s562 ++ (s607 ++ s648))) ++ ((s466 ++ (s766 ++ s823)) ++ (s877 ++ s912)))) ++ (((((s552 ++ s692) ++ (s578 ++ s774)) ++ (s731 ++ s222)) ++ (((s847 ++ s812) ++ (s611 ++ s681)) ++ (s283 ++ s870))) ++ ((s109 ++ (s210 ++ s354)) ++ (s388 ++ (((s712 ++ s778) ++ s683) ++ s653)))))) ++ ((((((s196 ++ s53) ++ ((s896 ++ s315) ++ (s152 ++ s636))) ++ (((s225 ++ s143) ++ (s555 ++ s286)) ++ (((s503 ++ s780) ++ s803) ++ (s1021 ++ s449)))) ++ (((s1022 ++ s40) ++ (s456 ++ s952)) ++ ((s331 ++ s517) ++ (s839 ++ s978)))) ++ ((((s719 ++ s904) ++ s12) ++ (((s624 ++ (s814 ++ s897)) ++ s37) ++ ((s922 ++ s604) ++ s434))) ++ ((((s773 ++ s859) ++ (s179 ++ s716)) ++ ((s566 ++ s986) ++ s332)) ++ ((s285 ++ (s594 ++ s443)) ++ s132)))) ++ (((((s439 ++ s360) ++ (s27 ++ s430)) ++ ((s791 ++ s577) ++ (s411 ++ s119))) ++ ((s514 ++ s146) ++ (((s647 ++ s690) ++ s677) ++ (s199 ++ s476)))) ++ (((s402 ++ (s551 ++ s488)) ++ s278) ++ ((s760 ++ s274) ++ s7))))) ++ (((((((s696 ++ s713) ++ s99) ++ (s216 ++ ((s576 ++ s373) ++ s886))) ++ ((s3 ++ s889) ++ (s630 ++ (s1005 ++ s857)))) ++ ((((s623 ++ s907) ++ (s335 ++ s586)) ++ ((s724 ++ s654) ++ (s994 ++ s502))) ++ (((s538 ++ s156) ++ (s463 ++ s440)) ++ (s242 ++ ((s401 ++ s261) ++ s709))))) ++ ((((((s51 ++ s1023) ++ s246) ++ (s448 ++ s587)) ++ ((s186 ++ s959) ++ (s901 ++ s784))) ++ (((s280 ++ s868) ++ ((s956 ++ s700) ++ (s362 ++ s413))) ++ (s248 ++ (s417 ++ s838)))) ++ ((((s275 ++ s903) ++ ((s909 ++ s807) ++ s431)) ++ ((s556 ++ s655) ++ (s384 ++ s554))) ++ (((s659 ++ (s876 ++ s1010)) ++ s480) ++ ((s865 ++ s105) ++ (s22 ++ s247)))))) ++ (((((s83 ++ ((s339 ++ s215) ++ s125)) ++ ((s334 ++ s593) ++ (s131 ++ s472))) ++ (((s710 ++ s799) ++ (s386 ++ s1016)) ++ ((s58 ++ s276) ++ s21))) ++ ((((s220 ++ (s426 ++ s357)) ++ (s46 ++ (s819 ++ s378))) ++ (((s776 ++ s232) ++ s827) ++ ((s717 ++ s782) ++ s204))) ++ ((s25 ++ s145) ++ (s975 ++ s805)))) ++ (((((s890 ++ s374) ++ s98) ++ (s2 ++ s591)) ++ (((s245 ++ s833) ++ s104) ++ ((s528 ++ s158) ++ s213))) ++ (((((s601 ++ s649) ++ (s606 ++ (s743 ++ s929))) ++ s201) ++ ((s752 ++ s91) ++ (s151 ++ s855))) ++ (((s893 ++ s708) ++ s612) ++ (s602 ++ s26)))))))) ++ (((((((((s432 ++ s629) ++ (s314 ++ s174)) ++ ((s324 ++ s492) ++ (s19 ++ s553))) ++ ((s923 ++ s8) ++ ((s988 ++ s234) ++ (s90 ++ s844)))) ++ ((((s438 ++ (s866 ++ s900)) ++ (s69 ++ (s737 ++ s993))) ++ ((s140 ++ ((s981 ++ s626) ++ s370)) ++ ((s342 ++ s511) ++ s821))) ++ (((s680 ++ s61) ++ s429) ++ (s403 ++ s926)))) ++ (((((s229 ++ s516) ++ (s967 ++ s157)) ++ (s962 ++ s16)) ++ ((((s460 ++ s735) ++ ((s895 ++ s998) ++ s835)) ++ s304) ++ ((s318 ++ s68) ++ (s369 ++ s881)))) ++ ((((s498 ++ s702) ++ s48) ++ (s45 ++ s149)) ++ (((s808 ++ s120) ++ ((s355 ++ s223) ++ s171)) ++ (s71 ++ ((s914 ++ s84) ++ (s1002 ++ s679))))))) ++ ((((((s1008 ++ s491) ++ (s525 ++ s277)) ++ (((s826 ++ s882) ++ s490) ++ s218)) ++ ((s138 ++ ((s790 ++ s964) ++ s867)) ++ (s32 ++ (s139 ++ s164)))) ++ (((((s465 ++ (s544 ++ s828)) ++ s268) ++ (s500 ++ (s557 ++ s971))) ++ (((s244 ++ s505) ++ s732) ++ s185)) ++ (((s999 ++ s854) ++ (s253 ++ s730)) ++ ((s95 ++ s723) ++ s1004)))) ++ ((((((s252 ++ s765) ++ (s235 ++ s884)) ++ (s524 ++ ((s745 ++ s938) ++ s851))) ++ (((s336 ++ s510) ++ (s86 ++ s741)) ++ s70)) ++ (((s584 ++ s494) ++ s1018) ++ (s38 ++ s451))) ++ ((((s209 ++ s711) ++ ((s816 ++ s995) ++ s837)) ++ ((s804 ++ s996) ++ (s299 ++ s224))) ++ ((s47 ++ ((s534 ++ s475) ++ (s960 ++ s772))) ++ ((s197 ++ s954) ++ (s177 ++ s682))))))) ++ (((((((s571 ++ s758) ++ s31) ++ ((s173 ++ s348) ++ (s834 ++ s748))) ++ (((s134 ++ s414) ++ s9) ++ (s395 ++ s684))) ++ (((((s419 ++ s136) ++ s237) ++ (s787 ++ s991)) ++ ((s757 ++ s352) ++ (s770 ++ s843))) ++ ((((s665 ++ s489) ++ (s461 ++ s933)) ++ (s236 ++ ((s596 ++ s477) ++ s672))) ++ ((s192 ++ s231) ++ (s663 ++ s537))))) ++ ((((((s361 ++ s801) ++ s946) ++ ((s794 ++ s453) ++ (s387 ++ s695))) ++ (s349 ++ s206)) ++ (((s303 ++ s282) ++ (s272 ++ s840)) ++ ((s496 ++ s479) ++ (s740 ++ s715)))) ++ (((((s704 ++ s526) ++ s697) ++ (s469 ++ s535)) ++ ((s685 ++ (s911 ++ s1000)) ++ (s455 ++ s316))) ++ ((s52 ++ (s617 ++ s824)) ++ (s265 ++ (s493 ++ s920)))))) ++ ((((((s820 ++ s574) ++ s542) ++ (s367 ++ s11)) ++ (((s227 ++ s1014) ++ (s825 ++ s883)) ++ (((s383 ++ s990) ++ s271) ++ s255))) ++ (((((s487 ++ s501) ++ s984) ++ (s376 ++ s583)) ++ ((s13 ++ s371) ++ s858)) ++ (((s862 ++ s141) ++ (s894 ++ s238)) ++ ((s619 ++ s330) ++ (s689 ++ s121))))) ++ (((((s759 ++ s93) ++ (s940 ++ s207)) ++ ((s916 ++ s102) ++ (s343 ++ s615))) ++ (((s656 ++ s436) ++ (s777 ++ s625)) ++ ((s111 ++ s20) ++ s166))) ++ (((((s830 ++ s167) ++ s1006) ++ (s885 ++ s404)) ++ ((s241 ++ (s575 ++ s705)) ++ (s291 ++ s393))) ++ ((((s254 ++ s942) ++ ((s478 ++ s905) ++ s341)) ++ ((s180 ++ s269) ++ s725)) ++ ((((s800 ++ s792) ++ s738) ++ (s714 ++ s836)) ++ (s658 ++ s364)))))))) ++ (((((((s319 ++ s240) ++ ((s590 ++ (s864 ++ s639)) ++ ((s930 ++ s670) ++ s641))) ++ ((s392 ++ s6) ++ ((s567 ++ s668) ++ (s499 ++ s739)))) ++ ((((s533 ++ (s983 ++ s811)) ++ (s570 ++ s147)) ++ (s43 ++ (s347 ++ s340))) ++ ((((s879 ++ s77) ++ s239) ++ (s118 ++ ((s963 ++ s693) ++ s955))) ++ (((s727 ++ s305) ++ s872) ++ (s849 ++ s75))))) ++ (((((s459 ++ s423) ++ s462) ++ ((s34 ++ s87) ++ s937)) ++ ((s628 ++ s10) ++ (s301 ++ (s425 ++ s810)))) ++ ((((s608 ++ s72) ++ ((s481 ++ s407) ++ (s226 ++ s973))) ++ (((s620 ++ s850) ++ s159) ++ ((s969 ++ s153) ++ s559))) ++ (((s1017 ++ s953) ++ (s148 ++ s28)) ++ (((s56 ++ s786) ++ s30) ++ ((s79 ++ s536) ++ (s418 ++ s124))))))) ++ ((((((s258 ++ ((s310 ++ s789) ++ (s1009 ++ s935))) ++ (((s323 ++ s892) ++ s483) ++ s308)) ++ (s175 ++ (s295 ++ s573))) ++ (((((s531 ++ s377) ++ s987) ++ s368) ++ (s669 ++ s297)) ++ (((s592 ++ s300) ++ (s749 ++ s359)) ++ (s421 ++ s170)))) ++ ((((s520 ++ s130) ++ (s365 ++ s250)) ++ s74) ++ ((((s447 ++ s736) ++ s842) ++ s80) ++ (((s822 ++ s764) ++ s809) ++ (s622 ++ s561))))) ++ ((((((s515 ++ s646) ++ s852) ++ (s168 ++ (s257 ++ s972))) ++ (s123 ++ s350)) ++ (((s767 ++ s521) ++ (s66 ++ s49)) ++ ((s163 ++ s845) ++ (s527 ++ s966)))) ++ (((s363 ++ s29) ++ (s112 ++ s564)) ++ ((s259 ++ (s322 ++ ((s880 ++ s932) ++ s428))) ++ ((s512 ++ s290) ++ (s958 ++ s1011))))))) ++ (((((((s522 ++ s707) ++ (s873 ++ s982)) ++ ((s144 ++ s256) ++ s631)) ++ (((s495 ++ s545) ++ (s267 ++ s908)) ++ (s1 ++ s264))) ++ (((s691 ++ s85) ++ (s454 ++ s97)) ++ ((((s888 ++ s543) ++ s874) ++ ((s742 ++ s445) ++ s585)) ++ ((s817 ++ s289) ++ s458)))) ++ (((((s337 ++ s519) ++ s292) ++ ((s530 ++ s279) ++ s94)) ++ (((s829 ++ s863) ++ (s721 ++ s182)) ++ ((s951 ++ s133) ++ s652))) ++ ((((s127 ++ s230) ++ s329) ++ ((s128 ++ s618) ++ s1020)) ++ ((s541 ++ (s795 ++ s1015)) ++ ((s391 ++ s1019) ++ s569))))) ++ (((((((s328 ++ s221) ++ s59) ++ ((s195 ++ s781) ++ (s581 ++ s270))) ++ (((s351 ++ (s424 ++ s661)) ++ (s394 ++ s632)) ++ s214)) ++ ((((s333 ++ (s390 ++ s565)) ++ s62) ++ s50) ++ ((((s627 ++ s187) ++ s1013) ++ (s260 ++ s470)) ++ (s486 ++ s142)))) ++ ((((s399 ++ (s409 ++ s945)) ++ ((s643 ++ s326) ++ s761)) ++ (s924 ++ s212)) ++ ((((s306 ++ s675) ++ s902) ++ ((s613 ++ s115) ++ s113)) ++ (s379 ++ s24)))) ++ ((((((s549 ++ s600) ++ (s621 ++ s783)) ++ s298) ++ ((s699 ++ s54) ++ s943)) ++ ((s609 ++ (s1001 ++ s768)) ++ ((s325 ++ s444) ++ s5))) ++ (((((s400 ++ s906) ++ (s802 ++ s81)) ++ s73) ++ (((s878 ++ s832) ++ (s666 ++ s676)) ++ s137)) ++ (((s762 ++ s734) ++ (s750 ++ s667)) ++ ((s17 ++ s546) ++ (s202 ++ s605)))))))))).
Proof.
Time autoperm.
(* Finished transaction in 75.369 secs (74.512u,0.596s) (successful) *)
Time Qed.
(* Finished transaction in 2.623 secs (2.608u,0.016s) (successful) *)

Print ex1.
