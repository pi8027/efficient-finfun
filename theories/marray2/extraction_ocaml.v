Require Import all_ssreflect all_algebra ordinal_ext core.
Require Extraction.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Load "../extraction_common.v".

(* nat *)

Extract Inlined Constant predn' => "(* predn' *)pred".

Extract Inlined Constant subn' => "(* subn' *)(-)".

(* ordinal *)

Extraction Inline
  lshift' rshift' ltnidx_l ltnidx_ls ltnidx_rp ord_pred ord_pred'.

(* finTypes *)

Extraction Inline
  fin_encode fin_decode
  Finite.mixin_base Finite.mixin_card Finite.mixin_encode Finite.mixin_decode
  Finite.base Finite.mixin Finite.base2 Finite.class Finite.clone
  Finite.eqType Finite.choiceType Finite.countType Finite.raw_card
  prod_fin_encode prod_fin_decode finfun_fin_encode finfun_fin_decode.

(* copyable structure *)

Extraction Implicit copyable_ffun [I].
Extraction Implicit copy_ffun [I].
Extract Inlined Constant copy_ffun => "Array.copy".

Extraction Inline Copyable.class copy finfun_copyType prod_copyType.

(* array state monad *)

Extraction Implicit astate_GET_ [I].
Extraction Implicit astate_SET_ [I].
Extraction Implicit astate_GET [I].
Extraction Implicit astate_SET [I].

Extract Inductive AState => "runt_AState"
  ["(* return *) (fun a s -> (a, s))"
   "(* bind *) (fun (f, g) s -> let (a, s') = f s in g a s')"
   "(* frameL *) (fun f (sl, sr) -> let (a, sl') = f sl in (a, (sl', sr)))"
   "(* frameR *) (fun f (sl, sr) -> let (a, sr') = f sr in (a, (sl, sr')))"
   "(* A *) (fun ((s, s'), s'') -> ((), (s, (s', s''))))"
   "(* A' *) (fun (s, (s', s'')) -> ((), ((s, s'), s'')))"
   "(* C *) (fun (s, s') -> ((), (s', s)))"
   "(* GET *) (fun i s -> (s.(i), s))"
   "(* SET *) (fun (i, x) s -> s.(i) <- x; ((), s))"]
  "(* It is not permitted to use AState_rect in extracted code. *)".
Extract Type Arity AState 1.

Extract Inlined Constant astate_ret => "(* return *) (fun a s -> (a, s))".
Extract Inlined Constant astate_bind =>
  "(* bind *) (fun f g s -> let (a, s') = f s in g a s')".
Extract Inlined Constant astate_frameL =>
  "(* frameL *) (fun f (sl, sr) -> let (a, sl') = f sl in (a, (sl', sr)))".
Extract Inlined Constant astate_frameR =>
  "(* frameR *) (fun f (sl, sr) -> let (a, sr') = f sr in (a, (sl, sr')))".
Extract Inlined Constant astate_A =>
  "(* A *) (fun ((s, s'), s'') -> ((), (s, (s', s''))))".
Extract Inlined Constant astate_A' =>
  "(* A' *) (fun (s, (s', s'')) -> ((), ((s, s'), s'')))".
Extract Inlined Constant astate_C => "(* C *) (fun (s, s') -> ((), (s', s)))".
Extract Inlined Constant astate_GET => "(* GET *) (fun i s -> (s.(i), s))".
Extract Inlined Constant astate_SET =>
  "(* SET *) (fun i x s -> s.(i) <- x; ((), s))".

Extract Constant run_AState_raw => "(* run_AState_raw *)".

Extraction Inline
  run_AState_raw run_AState SWAP swap
  iterate_revord iterate_fin iterate_revfin
  miterate_revord miterate_fin miterate_revfin.
