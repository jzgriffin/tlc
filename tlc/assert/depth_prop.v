From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat seq.
From tlc.utility
Require Import seq.
From tlc.assert
Require Import type rigid_var term atom prop lib interleavable_prop.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Inductive depth_prop {C} (d : seq nat) : @prop C -> Type :=
| DPCorrect t :
  depth_prop d (Atom (App TLC.correct t))
| DPEvent n d' o e :
  d' <<< d ->
  depth_prop d (TLC.IsOn n (TLC.IsEvent (@seq_to_term C Nat d') o e))
| DPNot p :
  depth_prop d p ->
  depth_prop d (Not p)
| DPOr p q :
  depth_prop d p ->
  depth_prop d q ->
  depth_prop d (Or p q)
| DPForall t (x : rigid_var t) p :
  depth_prop d p ->
  depth_prop d (Forall x p)
| DPUntil' p q :
  p <> Atom (@Const _ Bool false) ->
  depth_prop d p ->
  depth_prop d q ->
  depth_prop d (Until' p q)
| DPSince' p q :
  p <> Atom (@Const _ Bool false) ->
  depth_prop d p ->
  depth_prop d q ->
  depth_prop d (Since' p q).

Lemma depth_prop_is_interleavable {C} d p (DP : @depth_prop C d p)
: interleavable_prop p.
Proof.
  elim: DP; try by constructor;
  try by (rewrite /TLC.IsOn /TLC.IsEvent /TLC.Eq; repeat constructor).
Qed.
