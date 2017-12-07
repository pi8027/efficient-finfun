module Fw = Floyd_warshall;;
module FW = Fw.Floyd_Warshall;;

Random.self_init ();;

let gen_graph s elems =
  Random.init s;
  Array.init (elems * elems)
    (fun _ -> let n = Random.int 1000 in
              if n < 200 then Fw.Some n else Fw.None)
;;

let floyd_warshall_ocaml (n : int) g =
  let idx (x : int) (y : int) : int = x * n + y in
  for i = 0 to n - 1 do g.(idx i i) <- Fw.Some 0 done;
  for i = 0 to n - 1 do
    for j = 0 to n - 1 do
      match g.(idx j i) with
        | Fw.None -> ()
        | Fw.Some dji ->
          for k = 0 to n - 1 do
            match g.(idx i k), g.(idx j k) with
              | Fw.None, _ -> ()
              | Fw.Some dik, Fw.None ->
                g.(idx j k) <- Fw.Some (dji + dik)
              | Fw.Some dik, Fw.Some djk ->
                if dji + dik < djk
                then g.(idx j k) <- Fw.Some (dji + dik)
          done
    done
  done;
  g
;;

let i_max = 100 in
let j_max = 1 in
let seeds = Array.init (i_max * j_max) (fun _ -> Random.bits ()) in
for i_ = 0 to i_max - 1 do
  let i = (i_ + 1) * 10 in
  for j = 0 to j_max - 1 do
    let benchmark test =
      Utils.with_timer_median 5 (fun _ ->
        test i (gen_graph (seeds.(i_ * j_max + j)) i)) in
    let (time1, res1) = benchmark floyd_warshall_ocaml in
    let (time2, res2) = benchmark (fun n -> FW.floyd_warshall n) in
    let (time3, res3) = benchmark (fun n -> FW.floyd_warshall_fast n) in
    assert (res1 = res2); assert (res1 = res3);
    Printf.printf
      "[%d, %d] ocaml: %f, coq-pure: %f, coq-impure: %f%!\n"
      i j time1 time2 time3
  done
done
;;
