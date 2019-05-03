open Def.Presburger;;

let rec ppr_term t =
  "(" ^
  begin match t with
    | T_const n -> string_of_int n
    | T_var v -> "#" ^ string_of_int v
    | T_add (t1, t2) -> ppr_term t1 ^ " + " ^ ppr_term t2
    | T_mulc (n, t) -> string_of_int n ^ " * " ^ ppr_term t
  end ^ ")"
;;

let rec ppr_formula f =
  "(" ^
  begin match f with
    | F_all f -> "forall " ^ ppr_formula f
    | F_exists f -> "exists " ^ ppr_formula f
    | F_neg f -> "~ " ^ ppr_formula f
    | F_and (f1, f2) -> ppr_formula f1 ^ " /\\ " ^ ppr_formula f2
    | F_or (f1, f2) -> ppr_formula f1 ^ " \\/ " ^ ppr_formula f2
    | F_imply (f1, f2) -> ppr_formula f1 ^ " -> " ^ ppr_formula f2
    | F_leq (t1, t2) -> ppr_term t1 ^ " <= " ^ ppr_term t2
    | F_lt (t1, t2) -> ppr_term t1 ^ " < " ^ ppr_term t2
    | F_eq (t1, t2) -> ppr_term t1 ^ " = " ^ ppr_term t2
  end ^ ")"
;;

let formula_of_string str : int * formula =
  Pparser.main Plexer.token (Lexing.from_string str)
;;

let states vars f =
  let ch = finfun_finType (exp_finIndexType vars) bool_finType in
  let dfa = dfa_of_nformula vars (normal_f vars f) in
  string_of_int (CardDef.card dfa.dfa_state (fun _ -> true)) ^
  ", " ^
  string_of_int (List.length (enum_reachable ch dfa dfa.dfa_s))
;;

let sat vars f =
  let (time, res) =
    Utils.with_timer_median 5 (fun _ -> presburger_sat vars f) in
  (if res then "SAT" else "UNSAT") ^
  " (time: " ^ Utils.string_of_float time ^ "s)"
;;

let valid vars f =
  let (time, res) =
    Utils.with_timer_median 5 (fun _ -> presburger_valid vars f) in
  (if res then "VALID" else "INVALID") ^
  " (time: " ^ Utils.string_of_float time ^ "s)"
;;

let dec vars f =
  let (time, res) =
    Utils.with_timer_median 5 (fun _ -> presburger_st_dec f) in
  (if res then "TRUE" else "FALSE") ^
  " (time: " ^ Utils.string_of_float time ^ "s)"
;;

exception Invalid_Proc_Name of string;;
exception SIGINT;;

Sys.set_signal Sys.sigint
  (Sys.Signal_handle (fun _ -> print_newline (); raise SIGINT));;

while true do
    try
        print_string ">> ";
        let proc = match read_line () with
            | "STATES" -> states
            | "SAT" -> sat
            | "VALID" -> valid
            | "PP" -> (fun _ -> ppr_formula)
            | name -> raise (Invalid_Proc_Name name)
        in
        print_string ">>> ";
        let (vars, f) = formula_of_string (read_line ()) in
        print_endline ("<< " ^ proc vars f)
    with
        | Invalid_Proc_Name name ->
          print_endline ("<< Invalid procedure name: " ^ name)
        | SIGINT -> print_endline ("<< Interrupted")
        | End_of_file -> print_endline "\n<< Bye!"; exit 0
        | Stack_overflow -> print_endline "<< Stack overflow"
        | Parsing.Parse_error -> print_endline "<< Syntax error"
done
;;
