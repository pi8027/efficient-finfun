for i = 1 to 100 do
  let (time1, res1) =
    Utils.with_timer_median 5 (fun _ -> Matrix_before.matrix_mult_test i) in
  let (time2, res2) =
    Utils.with_timer_median 5 (fun _ -> Matrix_after.matrix_mult_test i) in
  assert (res1 = res2);
  Printf.printf "[%d] before: %f, after: %f\n" i time1 time2
done
;;
