From mathcomp.ssreflect
Require Import ssreflect.
From tlc.assert
Require Import type rigid_var term atom prop.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Inductive interleavable_prop {C} : @prop C -> Type :=
| IPAtom a :
  interleavable_prop (Atom a)
| IPNot p :
  interleavable_prop p ->
  interleavable_prop (Not p)
| IPOr p q :
  interleavable_prop p ->
  interleavable_prop q ->
  interleavable_prop (Or p q)
| IPForall t (x : rigid_var t) p :
  interleavable_prop p ->
  interleavable_prop (Forall x p)
| IPUntil' p q :
  p <> Atom (@Const _ Bool false) ->
  interleavable_prop p ->
  interleavable_prop q ->
  interleavable_prop (Until' p q)
| IPSince' p q :
  p <> Atom (@Const _ Bool false) ->
  interleavable_prop p ->
  interleavable_prop q ->
  interleavable_prop (Since' p q).

Definition interleavable_prop_t {C} := {p : @prop C & interleavable_prop p}.
