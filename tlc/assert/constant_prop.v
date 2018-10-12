From mathcomp.ssreflect
Require Import ssreflect.
From tlc.assert
Require Import rigid_var atom prop interleavable_prop.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Inductive constant_prop {C} : @prop C -> Type :=
| CAAtom a :
  constant_prop (Atom a)
| CAConj A1 A2 :
  constant_prop A1 ->
  constant_prop A2 ->
  constant_prop (Conj A1 A2)
| CANeg A0 :
  constant_prop A0 ->
  constant_prop (Neg A0)
| CAAlways t (x : rigid_var t) A0 :
  constant_prop A0 ->
  constant_prop (Always x A0).

Definition constant_prop_t {C} :=
  {A : @prop C & constant_prop A}.

Lemma constant_prop_is_interleavable {C} A
  (CA : @constant_prop C A) :
  interleavable_prop A.
Proof.
  elim: CA; by constructor.
Qed.
