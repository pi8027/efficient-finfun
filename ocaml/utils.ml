(* Utilities for benchmarking *)

let string_of_float f = Format.sprintf "%.03f" f;;

let with_timer f =
    let t = Sys.time () in
    let v = f () in
    (Sys.time () -. t, v)
;;

let median (xs : float list) : float =
  let sorted = List.sort compare xs in
  if List.length sorted mod 2 = 1
      then List.nth sorted (List.length sorted / 2)
      else (List.nth sorted (List.length sorted / 2 - 1) +.
            List.nth sorted (List.length sorted / 2)) /. 2.
;;

let with_timer_median n f =
    let time_list = ref [] in
    for i = 1 to n do
        Gc.full_major();
        let (time, _) = with_timer f in
        time_list := time :: !time_list
    done;
    (median !time_list, f ())
;;
