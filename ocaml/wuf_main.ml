type ufarray = (int, int) Wuf.sum array;;

let find (a : ufarray) x =
  let rec f x =
    match a.(x) with
      | Wuf.Inl x' -> let r = f x' in a.(x) <- Wuf.Inl (fst r) ; r
      | Wuf.Inr w -> (x, w)
  in f x
;;

let union (a : ufarray) x y : unit =
  let (x', wx) = find a x in
  let (y', wy) = find a y in
  if x' = y' then () else
  if wx <= wy
  then (a.(x') <- Wuf.Inl y'; a.(y') <- Wuf.Inr (wx + wy))
  else (a.(y') <- Wuf.Inl x'; a.(x') <- Wuf.Inr (wx + wy))
;;


let uftest1 (a : ufarray) elems n m =
  let pick () = Random.int elems in
  let rs : (int * int) list ref = ref [] in
  for i = 1 to n do
    let x = pick () in let y = pick () in union a x y
  done;
  for j = 1 to m do
    let x = pick () in let (r, _) = find a x in ()
  done
;;

let uftest2 (a : ufarray) elems n m =
  let indices_type = Wuf.ordinal_finType elems in
  let pick () = Obj.magic (Random.int elems) in
  let a' = Obj.magic ((), a) in
  let rs : (int * int) list ref = ref [] in
  for i = 1 to n do
    let x = pick () in let y = pick () in
    Wuf.WUF.munion indices_type x y a'
  done;
  for j = 1 to m do
    let x = pick () in let (r, _) = Wuf.WUF.mfind indices_type x a' in ()
  done
;;

(*
let uftest3 elems n m =
  let a1 : ufarray = Array.init elems (fun _ -> Wuf.Inr 1) in
  let a2 : ufarray = Array.init elems (fun _ -> Wuf.Inr 1) in
  let dump () =
    begin
      for i = 0 to elems - 1 do Printf.printf "%5d" i done; print_newline ();
      Array.iter (function Wuf.Inl x -> Printf.printf "%4dL" x
                         | Wuf.Inr r -> Printf.printf "%4dR" r) a1;
      print_newline ();
      Array.iter (function Wuf.Inl x -> Printf.printf "%4dL" x
                         | Wuf.Inr r -> Printf.printf "%4dR" r) a2;
      print_newline ();
    end in
  let a2' = Obj.magic ((), a2) in
  let indices_type = Wuf.ordinal_finType elems in
  let pick () = Random.int elems in
  for i = 1 to n do
    let x = pick () in let y = pick () in
    union a1 x y; Wuf.WUF.munion indices_type (Obj.magic x) (Obj.magic y) a2';
    print_endline ("union(" ^ string_of_int x ^ ", " ^ string_of_int y ^ ")");
    dump ()
  done;
  for i = 1 to m do
    let x = pick () in
    let (r1, _) = find a1 x in
    let (r2, _) = Wuf.WUF.mfind indices_type (Obj.magic x) a2' in
    print_endline
      (string_of_int x ^ ": " ^
       string_of_int r1 ^ ", " ^ string_of_int (Obj.magic r2));
  done
;;

let rec dump xs ys =
  match xs, ys with
    | (xl, xr) :: xs', (yl, yr) :: ys' ->
      print_endline ("((" ^ string_of_int xl ^ ", " ^ string_of_int xr ^ "), " ^
                      "(" ^ string_of_int yl ^ ", " ^ string_of_int yr ^ "))");
      dump xs' ys'
    | _ -> ()
;;
*)

Random.self_init ();;

let i_max = 200 in
let j_max = 5 in
let seeds = Array.init (i_max * j_max) (fun _ -> Random.bits ()) in
for i_ = 0 to i_max - 1 do
  let i = (i_ + 1) * 5000 in
  for j = 0 to j_max - 1 do
    Random.init (seeds.(i_ * j_max + j));
    let (time1, res1) =
      Utils.with_timer_median 3 (fun _ ->
        uftest1 (Array.init i (fun _ -> Wuf.Inr 1)) i i i) in
    Random.init (seeds.(i_ * j_max + j));
    let (time2, res2) =
      Utils.with_timer_median 3 (fun _ ->
        uftest2 (Array.init i (fun _ -> Wuf.Inr 1)) i i i) in
    (* assert (res1 = res2); *)
    print_endline
      ("[" ^ string_of_int i ^ ", " ^ string_of_int j ^ "] " ^
       "ocaml: " ^ Utils.string_of_float time1 ^ ", " ^
       "coq: " ^ Utils.string_of_float time2 ^ ", " ^
       "ratio: " ^ Utils.string_of_float (time2 /. time1))
  done
done
