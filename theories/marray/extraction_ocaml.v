From mathcomp Require Import all_ssreflect all_algebra.
Require Import core.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Set Extraction Conservative Types. *)
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
           ["0" "succ"]
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

(* ordinal *)

Extraction Implicit nat_of_ord [n].
Extract Inlined Constant nat_of_ord => "(* nat_of_ord *)".

Extraction Implicit cast_ord [n m].
Extract Inlined Constant cast_ord => "(* cast_ord *)".

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

Extraction Implicit tnth [n].
Extract Constant tnth => "Array.get". (*"(fun t i -> t.(i))"*)

(*
Extract Constant map_tuple => "(fun _ f t -> Array.map f t)".

Extract Constant ord_tuple => "(fun n -> Array.init n (fun n' -> n'))".
*)

Extract Constant codom_tuple =>
  "(fun t f ->
     Array.init
     t.Finite.mixin.Finite.mixin_card
     (fun i -> f (t.Finite.mixin.Finite.mixin_decode i)))".

Extraction Inline
  fin_encode fin_decode fun_of_fin finfun fgraph
  Finite.mixin_base Finite.mixin_card Finite.mixin_encode Finite.mixin_decode
  Finite.base Finite.mixin Finite.base2 Finite.class Finite.clone
  Finite.eqType Finite.choiceType Finite.countType Finite.raw_card
  ordinal_finType ordinal_finMixin ordinal_countType ordinal_countMixin
  ordinal_choiceType ordinal_choiceMixin ordinal_eqType ordinal_eqMixin
  prod_finType prod_finMixin prod_countType prod_countMixin
  prod_choiceType prod_choiceMixin prod_eqType prod_eqMixin
  prod_fin_encode.

(* avoiding extractor bugs: type mismatch, assertion failure, etc. *)

Extract Constant SetDef.pred_of_set =>
  "(fun t a -> Obj.magic FunFinfun.fun_of_fin
                 t ((set_subType t).val0 (Obj.magic a)))".

Extract Constant Finite.base2 =>
  "(fun c -> { Countable.base = c.base;
               Countable.mixin = (Obj.magic mixin_base __ c.mixin) })".

(* array state monad *)

Extraction Implicit astate_ret [sig].
Extraction Implicit astate_bind [sig].
Extraction Implicit astate_lift [Ix sig].
Extraction Implicit astate_GET [Ix sig].
Extraction Implicit astate_SET [Ix sig].

Extract Inductive AState => "runt_AState_"
  [" (fun a s -> a)"
   " (function (f, g) -> fun s -> let r = f s in g r s)"
   " (fun f s -> f (Obj.magic fst s))"
   " (fun i s -> (Obj.magic snd s).(i))"
   " (function (i, x) -> fun s -> (Obj.magic snd s).(i) <- x)"]
  "".
Extract Type Arity AState 1.

Extract Inlined Constant astate_ret => "(fun a s -> a)".
Extract Inlined Constant astate_bind =>
  "(fun f g s -> let r = f s in g r s)".
Extract Inlined Constant astate_lift =>
  "(fun f s -> f (Obj.magic fst s))".
Extract Inlined Constant astate_GET =>
  "(fun i s -> (Obj.magic snd s).(i))".
Extract Inlined Constant astate_SET =>
  "(fun i x s -> (Obj.magic snd s).(i) <- x)".

(*
Extract Inductive AState => "runt_AState_"
  [(* return *) " (fun a s -> a)"
   (* bind *)   " (function (f, g) -> fun s -> let r = f s in g r s)"
   (* lift *)   " (fun f s -> f (Obj.magic fst s))"
   (* get *)    " (fun i s -> (Obj.magic snd s).(i))"
   (* set *)    " (function (i, x) -> fun s -> (Obj.magic snd s).(i) <- x)"] "".
*)

Extract Constant run_AState =>
  "(fun sign f s ->
    let rec copy sign s =
      match sign with
        | [] -> Obj.magic ()
        | _ :: sign' -> let (s', a) = Obj.magic s in
          Obj.magic (copy sign' s', Array.copy a) in
    let s' = copy sign s in
    let r = Obj.magic f s' in (s', r))".

Extraction Implicit miterate_revord [sig n].
Extraction Implicit miterate_revfin [sig].
Extraction Implicit miterate_fin [sig].

Extraction Inline
  AState_monadType iterate_revfin iterate_fin miterate_revfin miterate_fin.

(*
Definition x Ix T sig A B (a : AState sig A) (f : A -> AState sig B) :=
  Eval simpl in @astate_lift Ix T _ _ (a' <- a; f a').
Definition y Ix T sig A B (a : AState sig A) (f : A -> AState sig B) :=
  Eval simpl in a' <- @astate_lift Ix T _ _ a; astate_lift (f a').

Extraction x.
Extraction y.
*)
