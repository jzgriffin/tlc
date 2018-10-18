From mathcomp.ssreflect
Require Import ssreflect.
From tlc.assert
Require Import prop top_prop.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Inductive top_inv {C} : @prop C -> Type :=
| TI p :
  top_prop p ->
  top_inv (Henceforth p).
