(* unit *)

Extract Inductive unit => "unit" ["()"].

Extraction Inline locked_with.

(* bool *)

Extract Inductive bool => "bool" ["true" "false"].

Extract Inductive reflect => "bool" ["true" "false"].

(*
Extract Inlined Constant negb => "not".
Extract Inlined Constant eqb => "((=) : bool -> bool -> bool)".
*)

Extraction Inline iffP idP.

(* prod *)

Extract Inductive prod => "( * )" ["(,)"].

(* list *)

Extract Inductive list => "list" ["[]" "(::)"].

Extraction Inline image_mem.

(* tag *)

Extraction Inline tag tagged Tagged.

(* nat *)

Extract Inductive
  nat => "int"
           ["0" "succ"]
           "(fun zero succ n -> if n = 0 then zero () else succ (n - 1))".

Extract Inlined Constant predn => "(fun n -> if n = 0 then 0 else n - 1)".

Extract Inlined Constant eqn => "((=) : int -> int -> bool)".
Extract Inlined Constant eqnP => "((=) : int -> int -> bool)".

Extract Inlined Constant addn_rec => "(+)".
Extract Inlined Constant addn => "(+)".

Extract Inlined Constant muln_rec => "( * )".
Extract Inlined Constant muln => "( * )".

Extract Inlined Constant subn_rec => "(fun n m -> if m <= n then n - m else 0)".
Extract Inlined Constant subn => "(fun n m -> if m <= n then n - m else 0)".

Extract Inlined Constant leq => "((<=) : int -> int -> bool)".

Extract Inlined Constant maxn => "(max : int -> int -> int)".

Extract Inlined Constant minn => "(min : int -> int -> int)".

Extract Inlined Constant nat_of_bool => "(fun b -> if b then 1 else 0)".

Extract Inlined Constant odd => "(fun n -> n mod 2 = 1)".

Extract Inlined Constant double_rec => "(fun n -> 2 * n)".
Extract Inlined Constant double => "(fun n -> 2 * n)".

Extract Inlined Constant edivn =>
  "(fun n m -> if m = 0 then Pair (0, n) else Pair (n / m, n mod m))".

Extract Inlined Constant divn => "(fun n m -> if m = 0 then 0 else n / m)".

Extract Inlined Constant modn => "(fun n m -> if m = 0 then n else n mod m)".

Extraction Inline leqP ltnP.

(* ordinal *)

Extraction Inline nat_of_ord cast_ord ord0 ord_max lshift rshift split.

(* int *)

Extract Inductive
  int => "int"
           ["(* Posz *)" "(fun n -> - (n + 1))"]
           "(fun pos neg n -> if 0 <= n then pos n else neg (- (n + 1)))".

Extract Inlined Constant intZmod.addz => "(+)".

Extract Inlined Constant intZmod.oppz => "(~-)".

Extract Inlined Constant intRing.mulz => "( * )".

Extract Inlined Constant absz => "abs".

Extract Inlined Constant intOrdered.lez => "(<=)".

Extract Inlined Constant intOrdered.ltz => "(<)".

(* function types *)

(*
Extract Inductive simpl_fun => "( -> )" ["(* SimplFun *)"] "(* simpl_fun_rec *)".

Extract Inductive mem_pred => "pred" ["(* Mem *)"] "(* mem_pred_rec *)".
*)

Extraction Inline Option.default Option.bind Option.map.

Extraction Inline
  fun_of_simpl funcomp pcomp
  SimplPred pred_of_simpl pred0 pred1 predT predI predU predC predD preim
  simpl_rel SimplRel rel_of_simpl_rel relU
  mkPredType predPredType simplPredType boolfunPredType seq_predType
  pred_of_mem memPredType sort_of_simpl_pred pred_of_argType mem in_mem
  pred_of_mem_pred has_quality.

(* eqTypes *)

Extraction Inline
  Equality.op Equality.class eq_op eqP
  nat_eqType nat_eqMixin int_eqType int_eqMixin
  unit_eqType unit_eqMixin bool_eqType bool_eqMixin
  option_eqType option_eqMixin
  prod_eqType prod_eqMixin pair_eq sum_eqType sum_eqMixin
  seq_eqType seq_eqMixin tuple_eqType tuple_eqMixin
  finfun_eqType finfun_of_eqType finfun_eqMixin
  set_eqType set_of_eqType set_eqMixin
  ordinal_eqType ordinal_eqMixin sub_eqType sub_eqMixin
  tag_eqType tag_eqMixin.

(* subTypes *)

Extraction Inline
  val Sub insub insubd
  ordinal_subType tuple_subType finfun_subType finfun_of_subType
  set_subType set_of_subType.

(* choiceTypes *)

Extraction Inline
  Choice.find Choice.base Choice.mixin Choice.class Choice.eqType
  Choice.InternalTheory.find
  nat_choiceType int_choiceType unit_choiceType bool_choiceType
  option_choiceType prod_choiceType sum_choiceType seq_choiceType
  tuple_choiceType
  finfun_choiceType finfun_of_choiceType set_choiceType set_of_choiceType
  ordinal_choiceType sub_choiceType tagged_choiceType.

(* countTypes *)

Extraction Inline
  Countable.pickle Countable.unpickle Countable.ChoiceMixin Countable.base
  Countable.mixin Countable.class Countable.choiceType pickle unpickle
  nat_countType int_countType unit_countType bool_countType option_countType
  prod_countType sum_countType seq_countType tuple_countType
  finfun_countType finfun_of_countType set_countType set_of_countType
  ordinal_countType sub_countType tag_countType.

(* finTypes *)

Extraction Inline
  Finite.EnumDef.enum enum_mem index_enum CardDef.card
  pred0b FiniteQuant.quant0b FiniteQuant.ex
  ordinal_finType ordinal_finMixin exp_finIndexType
  unit_finType unit_finMixin bool_finType bool_finMixin
  option_finType option_finMixin prod_finType prod_finMixin
  sum_finType sum_finMixin tuple_finType tuple_finMixin
  finfun_finType finfun_of_finType finfun_finMixin
  set_finType set_of_finType set_finMixin.

(* tuple and finfun *)

Extract Inductive
  tuple_of => "array"
                ["Array.of_list"]
                "(fun f t -> f (Array.to_list t))".

Extraction Implicit tnth_default [n].
Extraction Implicit tnth [n].
Extract Constant tnth => "Array.get".

Extract Constant ord_tuple => "(fun n -> Array.init n (fun n' -> n'))".

Extraction Implicit map_tuple [n].
Extract Constant map_tuple => "Array.map".

Extract Constant mktuple => "Array.init".

Extraction Inline
  tuple tval tcast fun_of_fin finfun fgraph finfun_of_set
  SetDef.finset SetDef.pred_of_set SetDef.finsetE SetDef.pred_of_setE.

(* algebra *)

Extraction Inline
  GRing.Zmodule.zero GRing.Zmodule.opp GRing.Zmodule.add GRing.Zmodule.mixin
  GRing.Zmodule.class GRing.Zmodule.sort GRing.Zmodule.pack
  GRing.Zmodule.eqType GRing.Zmodule.choiceType
  GRing.Ring.one GRing.Ring.mul GRing.Ring.EtaMixin GRing.Ring.base
  GRing.Ring.mixin GRing.Ring.class GRing.Ring.sort GRing.Ring.pack
  GRing.Ring.eqType GRing.Ring.choiceType GRing.Ring.zmodType
  GRing.ComRing.RingMixin GRing.ComRing.base GRing.ComRing.class
  GRing.ComRing.sort GRing.Ring.pack
  GRing.ComRing.eqType GRing.ComRing.choiceType GRing.ComRing.zmodType
  GRing.ComRing.ringType
  GRing.UnitRing.unit GRing.UnitRing.inv GRing.UnitRing.EtaMixin
  GRing.UnitRing.base GRing.UnitRing.mixin GRing.UnitRing.class
  GRing.UnitRing.sort GRing.UnitRing.pack
  GRing.UnitRing.eqType GRing.UnitRing.choiceType
  GRing.UnitRing.zmodType GRing.UnitRing.ringType
  GRing.ComUnitRing.Mixin GRing.ComUnitRing.base GRing.ComUnitRing.mixin
  GRing.ComUnitRing.base2 GRing.ComUnitRing.class GRing.ComUnitRing.sort
  GRing.ComUnitRing.pack
  GRing.ComUnitRing.eqType GRing.ComUnitRing.choiceType
  GRing.ComUnitRing.zmodType GRing.ComUnitRing.ringType
  GRing.ComUnitRing.comRingType GRing.ComUnitRing.unitRingType
  GRing.ComUnitRing.com_unitRingType
  GRing.IntegralDomain.base GRing.IntegralDomain.mixin
  GRing.IntegralDomain.class GRing.IntegralDomain.sort GRing.IntegralDomain.pack
  GRing.IntegralDomain.eqType GRing.IntegralDomain.choiceType
  GRing.IntegralDomain.zmodType GRing.IntegralDomain.ringType
  GRing.IntegralDomain.comRingType GRing.IntegralDomain.unitRingType
  GRing.IntegralDomain.comUnitRingType
  GRing.zero GRing.opp GRing.add GRing.natmul GRing.one GRing.mul.

Extraction Inline
  Num.norm_op Num.le_op Num.lt_op
  Num.NumDomain.base Num.NumDomain.mixin Num.NumDomain.class Num.NumDomain.pack
  Num.NumDomain.eqType Num.NumDomain.choiceType Num.NumDomain.zmodType
  Num.NumDomain.ringType Num.NumDomain.comRingType Num.NumDomain.unitRingType
  Num.NumDomain.comUnitRingType Num.NumDomain.idomainType
  Num.Def.ler Num.Def.ltr Num.Def.minr Num.Def.maxr.

Extraction Inline
  mx_val matrix_of_fun matrix_of_fun_def fun_of_matrix mulmx
  BigOp.bigop reducebig applybig
  intZmod.Mixin int_ZmodType intRing.comMixin int_Ring int_comRing
  intUnitRing.unitz intUnitRing.invz intUnitRing.comMixin
  int_unitRingType int_comUnitRing int_iDomain
  intOrdered.Mixin int_numDomainType int_realDomainType
  sgz.
