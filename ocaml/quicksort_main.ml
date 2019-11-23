module Qs = Quicksort;;
module QS = Qs.Quicksort;;
module Qs_o0 = Quicksort_o0;;
module QS_o0 = Qs_o0.Quicksort;;
module Ms = Mergesort;;
module MS = Ms.Mergesort;;
module MStail = Ms.Mergesort_tailrec;;

Random.self_init ();;

let gen_array s elems =
  Random.init s; Array.init elems (fun _ -> Random.int elems)
;;

let gen_list s elems =
  let rec glrec n acc =
    if n = 0 then acc else let x = Random.int elems in glrec (n - 1) (x :: acc) in
  Random.init s; List.rev (glrec elems [])
;;

let quicksort (cmp : 'a -> 'a -> bool) (arr : 'a array) : unit =
  let rec quicksort_rec (i : int) (j : int) : unit =
    if i < j then begin
    let pivot = arr.(i) in
    let i' = ref (i + 1) in
    let j' = ref j in
    let rec partition (_ : unit) : unit =
      while !i' <= j  && not (cmp pivot arr.(!i')) do i' := !i' + 1 done;
      while i   < !j' &&      cmp pivot arr.(!j')  do j' := !j' - 1 done;
      if !i' < !j'
      then let t = arr.(!i') in
           arr.(!i') <- arr.(!j'); arr.(!j') <- t; partition ()
    in
    partition ();
    arr.(i) <- arr.(!j');
    arr.(!j') <- pivot;
    quicksort_rec i (!j' - 1); quicksort_rec !i' j
    end
  in
  quicksort_rec 0 (Array.length arr - 1)
;;

let msort (cmp : 'a -> 'a -> int) (arr : 'a array) : unit =
  let merge src1 src2 dst l c r : unit =
    let rec loop i1 s1 i2 s2 d =
      if cmp s1 s2 <= 0 then begin
        dst.(d) <- s1;
        let i1 = i1 + 1 in
        if i1 < c then
          loop i1 src1.(i1) i2 s2 (d + 1)
        else
          Array.blit src2 i2 dst (d + 1) (r - i2)
      end else begin
        dst.(d) <- s2;
        let i2 = i2 + 1 in
        if i2 < r then
          loop i1 s1 i2 src2.(i2) (d + 1)
        else
          Array.blit src1 i1 dst (d + 1) (c - i1)
      end
    in loop l src1.(l) c src2.(c) l
  in

  let rec log2 (n : int) =
    if n <= 1 then 0 else 1 + log2 (n lsl 1)
  in
  let l = Array.length arr in
  let buf = Array.make l arr.(0) in
  let stack = Array.make (log2 (l + 3)) (0, 0) in

  let rec push top fl rb re depth =
    if top <= 0 || snd stack.(top - 1) != 0 then begin
      if 0 < top then begin
        let tval = stack.(top - 1) in
        stack.(top - 1) <- (fst tval, snd tval - 1)
      end;
      stack.(top) <- (rb, depth);
      top + 1
    end else begin
      let ofs1 = fst stack.(top - 1) in
      if fl then merge buf buf arr ofs1 rb re
            else merge arr arr buf ofs1 rb re;
      push (top - 1) (not fl) ofs1 re (depth + 1)
      end
  in

  let rec extract top fl rb =
    if top <= 0 then fl else
      let src2 = if fl then buf else arr in
      let fl = fl <> (snd stack.(top - 1) land 1 = 0) in
      let (src1, dst) = if fl then (arr, buf) else (buf, arr) in
      merge src1 src2 dst (fst stack.(top - 1)) rb l;
      extract (top - 1) fl (fst stack.(top - 1))
  in

  let rec rev b e =
    if b < e then
      let tmp = arr.(b) in
      arr.(b) <- arr.(e);
      arr.(e) <- tmp;
      rev (b + 1) (e - 1)
  in
  let rec loop top offset =
    let rec ascending offset =
      if offset + 1 < l && cmp arr.(offset) arr.(offset + 1) <= 0 then
        ascending (offset + 1)
      else
        offset
    in
    let rec descending offset =
      if offset + 1 < l && cmp arr.(offset) arr.(offset + 1) > 0 then
        descending (offset + 1)
      else
        offset
    in
    let offset' =
      if l <= offset + 1 then l else
        if cmp arr.(offset) arr.(offset + 1) <= 0 then
          ascending (offset + 1) + 1
        else
          let offset' = descending (offset + 1) in
          rev offset offset'; offset' + 1
    in
    if l <= offset' then begin
      begin if extract top false offset then Array.blit buf 0 arr 0 l end
    end else
      loop (push top false offset offset' 0) offset'
  in
  loop 0 0
;;

let i_max = 100 in
let j_max = 1 in
let seeds = Array.init (i_max * j_max) (fun _ -> Random.bits ()) in
for i_ = 0 to i_max - 1 do
  let i = (i_ + 1) * 100000 in
  for j = 0 to j_max - 1 do
    let benchmark (test : int -> int array -> int array) =
      Utils.with_timer_median 5 (fun _ ->
        test i (gen_array (seeds.(i_ * j_max + j)) i)) in
    let benchmarkl (test : int -> int list -> int list) =
      Utils.with_timer_median 5 (fun _ ->
        test i (gen_list (seeds.(i_ * j_max + j)) i)) in
    let (time1, res1) = benchmark
      (fun n arr -> let arr' = Array.copy arr in
                    Array.stable_sort Stdlib.compare arr'; arr') in
    let (time2, res2) = benchmark
      (fun n arr -> let arr' = Array.copy arr in
                    Array.sort Stdlib.compare arr'; arr') in
    let (time3, res3) = benchmark
      (fun n arr -> let arr' = Array.copy arr in
                    quicksort (<=) arr'; arr') in
    let (time4, res4) = benchmark
      (fun n arr -> let arr' = Array.copy arr in
                    msort Stdlib.compare arr'; arr') in
    let (time5, res5) = benchmark
      (fun n arr -> QS.quicksort_ (Qs.ordinal_finType n) (<=) arr) in
    let (time6, res6) = benchmark
      (fun n arr -> QS_o0.quicksort_ (Qs_o0.ordinal_finType n) (<=) arr) in
    let (time7, res7) =
      benchmarkl (fun n xs -> Obj.magic Ms.sort0 (<=) xs) in
    let (time8, res8) =
      benchmarkl (fun n xs -> Obj.magic MStail.sort (<=) xs) in
    assert (res1 = res2);
    assert (res1 = res3);
    assert (res1 = res4);
    assert (res1 = res5);
    assert (res1 = res6);
    assert (res1 = Array.of_list res7);
    assert (res7 = res8);
    Printf.printf
      "[%7d, %d] Array.stable_sort-o: %8.6f, Array.sort-o: %8.6f, \
                 Quicksort-o: %8.6f, Mergesort-o: %8.6f, \
                 Quicksort-c: %8.6f, Quicksort-co0: %8.6f, \
                 Mergesort1-c: %8.6f, Mergesort2-c: %8.6f%!\n"
      i j time1 time2 time3 time4 time5 time6 time7 time8
  done
done
;;
