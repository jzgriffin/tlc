From mathcomp.ssreflect
Require Import ssreflect ssrnat seq.
From tlc.assert
Require Import prop interleavable_prop depth_prop.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Inductive depth_inv {C} (d : seq nat) : @prop C -> Type :=
| DI p :
  depth_prop d p ->
  depth_inv d (Henceforth p).
