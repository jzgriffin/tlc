From mathcomp.ssreflect
Require Import ssreflect eqtype seq.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Class Promote (T : Type) := promote : T -> Type.

Instance promote_Type : Promote Type :=
  {
    promote t := t : Type
  }.

Instance promote_eqType : Promote eqType :=
  {
    promote t := t : Type
  }.

Instance promote_Set : Promote Set :=
  {
    promote t := t : Type
  }.

Definition promotes (T : Type) `{Promote T} (s : seq T) :=
  map promote s.
