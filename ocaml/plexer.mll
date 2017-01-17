{
open Pparser
}

rule token = parse
    [' ' '\t' '\n'] { token lexbuf }
  | ['a'-'z']+      { match Lexing.lexeme lexbuf with
                        | "forall" -> FORALL
                        | "exists" -> EXISTS
                        | str -> VAR str }
  | ['0'-'9']+      { CONST (int_of_string (Lexing.lexeme lexbuf)) }
  | "("             { LPAREN }
  | ")"             { RPAREN }
  | "~"             { NEG }
  | "/\\"           { AND }
  | "\\/"           { OR }
  | "->"            { IMPLY }
  | "<->"           { IFF }
  | "<="            { LE }
  | "<"             { LT }
  | "="             { EQ }
  | "+"             { ADD }
  | "|"             { DIVISIBLE }
  | "."             { DOT }
  | ";"             { SEMICOLON }
  | eof             { EOF }
