From mathcomp.ssreflect
Require Import ssreflect.

Require Import assertion.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Inductive Interleavable : assertion -> Type :=
| Interleavable_false :
  Interleavable Afalse
| Interleavable_pred p ts :
  Interleavable (Apred p ts)
| Interleavable_conj A1 A2 :
  Interleavable A1 ->
  Interleavable A2 ->
  Interleavable (Aconj A1 A2)
| Interleavable_neg A :
  Interleavable A ->
  Interleavable (Aneg A)
| Interleavable_univ x A :
  Interleavable A ->
  Interleavable (Auniv x A)
| Interleavable_alwaysfs A :
  Interleavable A ->
  Interleavable (Aalwaysfs A)
| Interleavable_alwaysps A :
  Interleavable A ->
  Interleavable (Aalwaysps A)
| Interleavable_eventfs A :
  Interleavable A ->
  Interleavable (Aeventfs A)
| Interleavable_eventps A :
  Interleavable A ->
  Interleavable (Aeventps A).

Notation InterleavableAssertionT :=
  {x : assertion & Interleavable x}
  (only parsing).
