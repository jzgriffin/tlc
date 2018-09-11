From mathcomp.ssreflect
Require Import ssreflect eqtype.

Require Import term assertion stackassertion.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Inductive StackInvariant (d : term) : assertion -> Prop :=
| StackInvariant_alwaysf A :
  StackInvariant d A ->
  StackInvariant d (Aalwaysf A).
