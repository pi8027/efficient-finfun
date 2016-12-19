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

for i = 1 to 100 do
    let b_list = ref [] in
    let a_list = ref [] in
    for j = 1 to 5 do
        let (b_time, b_res) =
          with_timer (fun _ -> Matrix_before.matrix_mult_test i) in
        let (a_time, a_res) =
          with_timer (fun _ -> Matrix_after.matrix_mult_test i) in
        b_list := b_time :: !b_list;
        a_list := a_time :: !a_list
    done;
    print_endline ("[" ^ string_of_int i ^ "] " ^
                   "before: " ^ string_of_float (median !b_list) ^ ", " ^
                   "after: "  ^ string_of_float (median !a_list))
done
;;
