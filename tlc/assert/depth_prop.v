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
| DACorrect t :
  depth_prop d (Atom (App TLC.correct t))
| DAEv n d' o e :
  d' <<< d ->
  depth_prop d (TLC.On n (TLC.Ev (@seq_to_term C Nat d') o e))
| DAConj A1 A2 :
  depth_prop d A1 ->
  depth_prop d A2 ->
  depth_prop d (Conj A1 A2)
| DANeg A0 :
  depth_prop d A0 ->
  depth_prop d (Neg A0)
| DAAlways t (x : rigid_var t) A0 :
  depth_prop d A0 ->
  depth_prop d (Always x A0)
| DAAlwaysF' A0 :
  depth_prop d A0 ->
  depth_prop d (AlwaysF' A0)
| DAAlwaysP' A0 :
  depth_prop d A0 ->
  depth_prop d (AlwaysP' A0)
| DAExistsF' A0 :
  depth_prop d A0 ->
  depth_prop d (ExistsF' A0)
| DAExistsP' A0 :
  depth_prop d A0 ->
  depth_prop d (ExistsP' A0).

Lemma depth_prop_is_interleavable {C} d A
  (DA : @depth_prop C d A) :
  interleavable_prop A.
Proof.
  elim: DA; try by constructor;
  try by (rewrite /TLC.On /TLC.Ev /TLC.Eq; repeat constructor).
Qed.
