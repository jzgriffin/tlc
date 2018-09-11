From mathcomp.ssreflect
Require Import ssreflect.

Require Import assertion.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Inductive NonTemporal : assertion -> Prop :=
| NonTemporal_false :
  NonTemporal Afalse
| NonTemporal_pred p ts :
  NonTemporal (Apred p ts)
| NonTemporal_conj A1 A2 :
  NonTemporal A1 ->
  NonTemporal A2 ->
  NonTemporal (Aconj A1 A2)
| NonTemporal_neg A :
  NonTemporal A ->
  NonTemporal (Aneg A)
| NonTemporal_univ x A :
  NonTemporal A ->
  NonTemporal (Auniv x A).
