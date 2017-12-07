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

(* array state monad *)

Extraction Implicit astate_ret_ [sig].
Extraction Implicit astate_bind_ [sig].
Extraction Implicit astate_lift_ [I sig].
Extraction Implicit astate_GET_ [I sig].
Extraction Implicit astate_SET_ [I sig].
Extraction Implicit astate_ret [sig].
Extraction Implicit astate_bind [sig].
Extraction Implicit astate_lift [I sig].
Extraction Implicit astate_GET [I sig].
Extraction Implicit astate_SET [I sig].

Extract Inductive AState => "runt_AState_"
  [(* return *) " (fun a s -> a)"
   (* bind *)   " (fun (f, g) s -> let r = f s in g r s)"
   (* lift *)   " (fun f s -> let (ss, _) = Obj.magic s in f ss)"
   (* get *)    " (fun i s -> let (_, s1) = Obj.magic s in s1.(i))"
   (* set *)    " (fun (i, x) s -> let (_, s1) = Obj.magic s in s1.(i) <- x)"]
  "(* It is not permitted to use AState_rect in extracted code. *)".
Extract Type Arity AState 1.

Extract Inlined Constant astate_ret => "(fun a s -> a)".
Extract Inlined Constant astate_bind => "(fun f g s -> let r = f s in g r s)".
Extract Inlined Constant astate_lift =>
  "(fun f s -> let (ss, _) = Obj.magic s in f ss)".
Extract Inlined Constant astate_GET =>
  "(fun i s -> let (_, s1) = Obj.magic s in s1.(i))".
Extract Inlined Constant astate_SET =>
  "(fun i x s -> let (_, s1) = Obj.magic s in s1.(i) <- x)".

Extract Constant run_AState =>
  "(fun sign f s ->
    let rec copy sign s =
      match sign with
        | [] -> Obj.magic ()
        | _ :: sign' -> let (s', a) = Obj.magic s in
          Obj.magic (copy sign' s', Array.copy a) in
    let s' = copy sign s in
    let r = Obj.magic f s' in (s', r))".

Extraction Inline
  Monad.base Monad.runt Monad.run Monad.ret Monad.bind
  Identity_monadType AState_monadType
  SWAP swap
  iterate_revord iterate_fin iterate_revfin
  miterate_revord miterate_fin miterate_revfin.
