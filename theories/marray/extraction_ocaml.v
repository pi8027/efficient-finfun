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

(* copyTypes *)

Extraction Implicit ffun_copy [I].
Extract Inlined Constant ffun_copy => "Array.copy".

Extraction Inline
  CopyableRaw.copy CopyableRaw.ffun_mixin CopyableRaw.prod_mixin
  Copyable.class Copyable.pack Copyable.clone
  copy finfun_copyType prod_copyType.

(* array state monad *)

Extraction Implicit astate_GET_ [I].
Extraction Implicit astate_SET_ [I].
Extraction Implicit astate_GET [I].
Extraction Implicit astate_SET [I].

Extract Inductive AState => "(->)"
  [(* return *) "(fun a s -> a)"
   (* bind *)   "(fun (f, g) s -> let r = f s in g r s)"
   (* frameL *) "(fun f (sl, _) -> f sl)"
   (* frameR *) "(fun f (_, sr) -> f sr)"
   (* get *)    "(fun i s -> s.(i))"
   (* set *)    "(fun (i, x) s -> s.(i) <- x)"]
  "(* It is not permitted to use AState_rect in extracted code. *)".
Extract Type Arity AState 1.

Extract Inlined Constant astate_ret =>
  "(* return *) (fun a s -> a)".
Extract Inlined Constant astate_bind =>
  "(* bind *) (fun f g s -> let r = f s in g r s)".
Extract Inlined Constant astate_frameL =>
  "(* frameL *) (fun f (sl, _) -> f sl)".
Extract Inlined Constant astate_frameR =>
  "(* frameR *) (fun f (_, sr) -> f sr)".
Extract Inlined Constant astate_GET =>
  "(* GET *) (fun i s -> s.(i))".
Extract Inlined Constant astate_SET =>
  "(* SET *) (fun i x s -> s.(i) <- x)".
Extract Inlined Constant run_AState_raw =>
  "(* run_AState_raw *) (fun a s -> (a s, s))".

Extraction Inline
  run_AState
  SWAP swap
  iterate_revord iterate_fin iterate_revfin
  miterate_revord miterate_fin miterate_revfin.
