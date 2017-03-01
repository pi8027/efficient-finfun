From mathcomp Require Import all_ssreflect all_algebra.
Require Import core.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Extraction Language Ocaml.

(* unit *)

Extract Inductive unit => "unit" [" () "].

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

(*
Extract Constant map_tuple => "(fun _ f t -> Array.map f t)".

Extract Constant ord_tuple => "(fun n -> Array.init n (fun n' -> n'))".
*)

Extract Constant codom_tuple =>
  "(fun t f ->
     Array.init
     t.Finite.mixin.Finite.mixin_card
     (fun i -> f (EncDecDef.fin_decode t i)))".

Extract Constant EncDecDef.fin_encode =>
  "(fun t x -> (Finite.coq_class t).Finite.mixin.Finite.mixin_encode x)".

Extract Constant EncDecDef.fin_decode =>
  "(fun t i -> (Finite.coq_class t).Finite.mixin.Finite.mixin_decode i)".

Extract Constant FunFinfun.fun_of_fin =>
  "(fun aT f x -> f.(EncDecDef.fin_encode aT x))".

(* array state monad *)

Extract Inductive AState => "runt_AState_"
  [" (function (_, a) -> fun s -> a)"
   " (function (_, f, g) -> fun s -> let r = f s in g r s)"
   " (function (_, _, f) -> fun s -> f (Obj.magic fst s))"
   " (function (ix, _, i) -> fun s -> (Obj.magic snd s).(i))"
   " (function (ix, _, i, x) -> fun s -> (Obj.magic snd s).(i) <- x)"] "".

(*
Extract Inductive AState => "runt_AState_"
  [" ((* astate_ret  *) fun p s -> let (_, a) = p in a)"
   " ((* astate_bind *) fun p s -> let (_, f, g) = p in
                        let r = f s in g r s)"
   " ((* astate_lift *) fun p s -> let (_, _, f) = p in f (Obj.magic fst s))"
   " ((* astate_get  *) fun p s -> let (ix, _, i) = p in
                          (Obj.magic snd s).(EncDecDef.fin_encode ix i))"
   " ((* astate_set  *) fun p s -> let (ix, _, i, x) = p in
                          (Obj.magic snd s).(EncDecDef.fin_encode ix i) <- x)"]
  "".
*)

Extract Constant run_AState =>
  "(fun sign f s ->
    let rec copy sign =
      match sign with
        | [] -> Obj.magic ()
        | _ :: sign' -> let (s', a) = Obj.magic s in
          Obj.magic (copy sign' s', Array.copy a) in
    let s' = copy sign s in
    let r = Obj.magic f sign s' in (s', r))".
