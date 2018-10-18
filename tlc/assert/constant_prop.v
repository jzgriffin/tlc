From mathcomp.ssreflect
Require Import ssreflect.
From tlc.assert
Require Import rigid_var atom prop interleavable_prop.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Inductive constant_prop {C} : @prop C -> Type :=
| CPAtom a :
  constant_prop (Atom a)
| CPNot p :
  constant_prop p ->
  constant_prop (Not p)
| CPOr p q :
  constant_prop p ->
  constant_prop q ->
  constant_prop (Or p q)
| CPForall t (x : rigid_var t) p :
  constant_prop p ->
  constant_prop (Forall x p).

Definition constant_prop_t {C} := {p : @prop C & constant_prop p}.

Lemma constant_prop_is_interleavable {C} p (CP : @constant_prop C p)
: interleavable_prop p.
Proof.
  elim: CP; by constructor.
Qed.
