module Qs = Quicksort;;
module QS = Qs.Quicksort;;
module MS = Qs.Mergesort;;

Random.self_init ();;

let gen_array s elems =
  Random.init s; Array.init elems (fun _ -> Random.int elems)
;;

let gen_list s elems =
  let rec glrec n =
    if n = 0 then [] else let x = Random.int elems in x :: glrec (n - 1) in
  Random.init s; glrec elems
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
  let i = (i_ + 1) * 1000 in
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
    let (time5, res5) = benchmarkl
      (fun n xs -> Obj.magic MS.mergesort Qs.nat_eqType (<=) xs) in
    assert (res1 = res2);
    assert (res1 = res3);
    assert (res1 = res4);
    assert (res1 = Array.of_list res5);
    Printf.printf
      "[%6d, %d] Array.stable_sort-o: %6.3f, Array.sort-o: %6.3f, \
                 Quicksort-o: %6.3f, Quicksort-c: %6.3f, Mergesort-c: %6.3f%!\n"
      i j (1000. *. time1) (1000. *. time2) (1000. *. time3) (1000. *. time4)
      (1000. *. time5)
  done
done
;;
