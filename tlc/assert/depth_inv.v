From mathcomp.ssreflect
Require Import ssreflect ssrnat seq.
From tlc.assert
Require Import prop interleavable_prop depth_prop.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Inductive depth_inv {C} (d : seq nat) : @prop C -> Type :=
| DI A :
  depth_prop d A ->
  depth_inv d (AlwaysF A).
