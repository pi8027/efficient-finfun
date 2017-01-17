for i = 1 to 100 do
    let b_result =
      Utils.with_timer_median 5 (fun _ -> Matrix_before.matrix_mult_test i) in
    let a_result =
      Utils.with_timer_median 5 (fun _ -> Matrix_after.matrix_mult_test i) in
    print_endline
      ("[" ^ string_of_int i ^ "] " ^
       "before: " ^ Utils.string_of_float (fst b_result) ^ ", " ^
       "after: "  ^ Utils.string_of_float (fst a_result))
done
;;
