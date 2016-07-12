Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import all_ssreflect all_algebra.
Require Import presburger.

Extraction Language Ocaml.

(* bool *)

Extract Inductive bool => "bool" ["true" "false"].

Extract Inductive reflect => "bool" ["true" "false"].

Extract Inductive
  Equality.mixin_of => "rel" ["fst"] "(fun f eq -> f eq eq)".

(* prod *)

Extract Inductive prod => "( * )" ["(,)"].

(* list *)

Extract Inductive list => "list" ["[]" "(::)"].

(* nat *)

Extract Inductive
  nat => "int"
           ["0" "(fun n -> n + 1)"]
           "(fun zero succ n -> if n = 0 then zero () else succ (n - 1))".

Extract Inlined Constant predn => "(fun n -> if n = 0 then 0 else n - 1)".

Extract Inlined Constant eqn => "(fun n m -> n = m)".

Extract Inlined Constant addn_rec => "(+)".
Extract Inlined Constant addn => "(+)".

Extract Inlined Constant muln_rec => "( * )".
Extract Inlined Constant muln => "( * )".

Extract Inlined Constant subn_rec => "(fun n m -> if m <= n then n - m else 0)".
Extract Inlined Constant subn => "(fun n m -> if m <= n then n - m else 0)".

Extract Inlined Constant leq => "(<=)".

Extract Inlined Constant maxn => "max".

Extract Inlined Constant minn => "min".

Extract Inlined Constant nat_of_bool => "(fun b -> if b then 1 else 0)".

Extract Inlined Constant odd => "(fun n -> n mod 2 = 1)".

Extract Inlined Constant double_rec => "(fun n -> 2 * n)".
Extract Inlined Constant double => "(fun n -> 2 * n)".

Extract Inlined Constant edivn =>
  "(fun n m -> if m = 0 then Pair (0, n) else Pair (n / m, n mod m))".

Extract Inlined Constant divn => "(fun n m -> if m = 0 then 0 else n / m)".

Extract Inlined Constant modn => "(fun n m -> if m = 0 then n else n mod m)".

Extract Inlined Constant nat_of_ord => "(fun _ i -> i)".

(* int *)

Extract Inductive
  int => "int"
           ["" "(fun n -> - (n + 1))"]
           "(fun pos neg n -> if 0 <= n then pos n else neg (- (n + 1)))".

Extract Inlined Constant intZmod.addz => "(+)".

Extract Inlined Constant intZmod.oppz => "(~-)".

Extract Inlined Constant intRing.mulz => "( * )".

Extract Inlined Constant absz => "abs".

Extract Inlined Constant intOrdered.lez => "(<=)".

Extract Inlined Constant intOrdered.ltz => "(<)".

(* function types *)

Extract Inductive simpl_fun => "( -> )" [""] "".

Extract Inductive mem_pred => "pred" [""] "".

Extract Inlined Constant SimplPred => "".

Extract Inlined Constant fun_of_simpl => "".

Extract Inlined Constant pred_of_simpl => "".

(* tuple and finfun *)

Extract Inductive
  tuple_of => "array"
                ["Array.of_list"]
                "(fun f t -> f (Array.to_list t))".

Extract Constant tnth => "(fun _ t i -> t.(i))".

Extract Constant map_tuple => "(fun _ f t -> Array.map f t)".

Extract Constant ord_tuple => "(fun n -> Array.init n (fun n' -> n'))".

Extraction "../ocaml/presburger_before.ml"
           f_divisible dfa_prune
           presburger_dec presburger_st_dec presburger_sat presburger_valid.

(* matrix *)

Definition matrix_mult_test (n : nat) :=
  let mx := (\matrix_(i < n.+1, j < n.+1) (i%:Z + j%:Z))%R in
  (mx *m mx)%R.

Definition finfun_app_test (n : nat) :=
  let f := [ffun i : 'I_n => i] in
  \sum_i f i.

Extraction "../ocaml/matrix_before.ml" matrix_mult_test finfun_app_test.
