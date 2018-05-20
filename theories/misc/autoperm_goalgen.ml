let rec iota n m =
  if m = 0 then [] else n :: iota (n + 1) (m - 1)
;;

let rec split_random = function
  | [] -> ([], [])
  | x :: xs ->
    let (ys, zs) = split_random xs in
    if Random.bool () then (x :: ys, zs) else (ys, x :: zs)
;;

let rec termgen = function
  | [] -> "[::]"
  | [x] -> x
  | x :: xs ->
    let (ys, zs) = split_random xs in
    if List.length ys <= List.length zs then
      "(" ^ termgen (x :: ys) ^ " ++ " ^ termgen zs ^ ")"
    else
      "(" ^ termgen ys ^ " ++ " ^ termgen (x :: zs) ^ ")"
;;

let xs =
  List.map (fun n -> "s" ^ string_of_int n) (iota 0 64)
in
print_string  "Example ex (A : eqType) (";
print_string  (String.concat " " xs);
print_endline ": seq A) :";
print_string  "  perm_eq ";
print_endline (termgen xs);
print_string  "          ";
print_string (termgen xs);
print_endline "."
