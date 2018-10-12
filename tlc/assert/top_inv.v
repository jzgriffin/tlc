From mathcomp.ssreflect
Require Import ssreflect.
From tlc.assert
Require Import prop top_prop.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Inductive top_inv {C} : @prop C -> Type :=
| TI A :
  top_prop A ->
  top_inv (AlwaysF A).
