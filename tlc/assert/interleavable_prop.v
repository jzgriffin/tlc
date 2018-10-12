From mathcomp.ssreflect
Require Import ssreflect.
From tlc.assert
Require Import rigid_var atom prop.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Inductive interleavable_prop {C} : @prop C -> Type :=
| IAAtom a :
  interleavable_prop (Atom a)
| IAConj A1 A2 :
  interleavable_prop A1 ->
  interleavable_prop A2 ->
  interleavable_prop (Conj A1 A2)
| IANeg A0 :
  interleavable_prop A0 ->
  interleavable_prop (Neg A0)
| IAAlways t (x : rigid_var t) A0 :
  interleavable_prop A0 ->
  interleavable_prop (Always x A0)
| IAAlwaysF' A0 :
  interleavable_prop A0 ->
  interleavable_prop (AlwaysF' A0)
| IAAlwaysP' A0 :
  interleavable_prop A0 ->
  interleavable_prop (AlwaysP' A0)
| IAExistsF' A0 :
  interleavable_prop A0 ->
  interleavable_prop (ExistsF' A0)
| IAExistsP' A0 :
  interleavable_prop A0 ->
  interleavable_prop (ExistsP' A0).

Definition interleavable_prop_t {C} :=
  {A : @prop C & interleavable_prop A}.
