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
                    Array.stable_sort Pervasives.compare arr'; arr') in
    let (time2, res2) = benchmark
      (fun n arr -> let arr' = Array.copy arr in
                    Array.sort Pervasives.compare arr'; arr') in
    let (time3, res3) = benchmark
      (fun n arr -> let arr' = Array.copy arr in
                    quicksort (<=) arr'; arr') in
    let (time4, res4) = benchmark
      (fun n arr -> QS.quicksort_ (Qs.ordinal_finType n) (<=) arr) in
    let (time5, res5) = benchmark
      (fun n arr -> QS_o0.quicksort_ (Qs_o0.ordinal_finType n) (<=) arr) in
    let (time6, res6) =
      benchmarkl (fun n xs -> Obj.magic MStail.sort (<=) xs) in
    assert (res1 = res2);
    assert (res1 = res3);
    assert (res1 = res4);
    assert (res1 = res5);
    assert (res1 = Array.of_list res6);
    Printf.printf
      "[%7d, %d] Array.stable_sort-o: %8.6f, Array.sort-o: %8.6f, \
                 Quicksort-o: %8.6f, Quicksort-c: %8.6f, Quicksort-co0: %8.6f, \
                 Mergesort1-c: %8.6f%!\n"
      i j time1 time2 time3 time4 time5 time6
  done
done
;;
