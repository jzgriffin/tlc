From mathcomp.ssreflect
Require Import ssreflect eqtype ssrbool seq.
From tlc.utility
Require Import seq.

Require Import term predicate assertion.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Inductive StackAssertion (d : term) : assertion -> Prop :=
| StackAssertion_correct t :
  StackAssertion d (Apred Pcorrect [:: t])
| StackAssertion_event n d' o e :
  seq_term d' <<< seq_term d ->
  StackAssertion d (Aon n (Aev d' o e))
| StackAssertion_conj A1 A2 :
  StackAssertion d A1 ->
  StackAssertion d A2 ->
  StackAssertion d (Aconj A1 A2)
| StackAssertion_neg A :
  StackAssertion d A ->
  StackAssertion d (Aneg A)
| StackAssertion_univ x A :
  StackAssertion d A ->
  StackAssertion d (Auniv x A)
| StackAssertion_alwaysfs A :
  StackAssertion d A ->
  StackAssertion d (Aalwaysfs A)
| StackAssertion_alwaysps A :
  StackAssertion d A ->
  StackAssertion d (Aalwaysps A)
| StackAssertion_eventfs A :
  StackAssertion d A ->
  StackAssertion d (Aeventfs A)
| StackAssertion_eventps A :
  StackAssertion d A ->
  StackAssertion d (Aeventps A).
