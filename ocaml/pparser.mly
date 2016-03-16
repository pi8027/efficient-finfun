%{
open Def;;

let rec index xs y =
    match xs with
        | [] -> raise Not_found
        | x :: xs' -> if x = y then 0 else index xs' y + 1
;;
%}
%token <string> VAR
%token <int> CONST
%token LPAREN RPAREN
%token FORALL EXISTS DOT NEG AND OR IMPLY LE LT EQ
%token ADD DIVISIBLE
%token EOF SEMICOLON
%start main
%type <int * Def.Presburger.formula> main
%type <(string list -> Def.Presburger.formula)> formula1
%%

main: formula EOF { $1 }

term3:
    CONST                   { fun ns -> Presburger.T_const $1 }
  | VAR                     { fun ns -> Presburger.T_var (index ns $1) }
  | LPAREN term1 RPAREN     { $2 }

term2:
  | CONST term3             { fun ns -> Presburger.T_mulc ($1, $2 ns) }
  | term3                   { $1 }

term1:
  | term1 ADD term2         { fun ns -> Presburger.T_add ($1 ns, $3 ns) }
  | term2                   { $1 }

formula4:
  | FORALL VAR DOT formula1 { fun ns -> Presburger.F_all ($4 ($2 :: ns)) }
  | EXISTS VAR DOT formula1 { fun ns -> Presburger.F_exists ($4 ($2 :: ns)) }
  | NEG formula4            { fun ns -> Presburger.F_neg ($2 ns) }
  | term1 LE term1          { fun ns -> Presburger.F_leq ($1 ns, $3 ns) }
  | term1 LT term1          { fun ns -> Presburger.F_lt ($1 ns, $3 ns) }
  | term1 EQ term1          { fun ns -> Presburger.F_eq ($1 ns, $3 ns) }
  | CONST DIVISIBLE term2   { fun ns -> Presburger.f_divisible (List.length ns) $1 ($3 ns) }
  | LPAREN formula1 RPAREN  { $2 }

formula3:
  | formula3 AND formula4   { fun ns -> Presburger.F_and ($1 ns, $3 ns) }
  | formula4                { $1 }

formula2:
  | formula2 OR formula3    { fun ns -> Presburger.F_or ($1 ns, $3 ns) }
  | formula3                { $1 }

formula1:
  | formula2 IMPLY formula1 { fun ns -> Presburger.F_imply ($1 ns, $3 ns) }
  | formula2                { $1 }

names:
  | VAR SEMICOLON names     { $1 :: $3 }
  | VAR                     { [$1] }

formula:
  | LPAREN RPAREN formula1  { (0, $3 []) }
  | LPAREN names RPAREN formula1 { (List.length $2, $4 $2) }
