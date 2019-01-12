Require Import Coq.Vectors.Fin.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Notation scope *)
Delimit Scope fin_scope with fin.
Bind Scope fin_scope with Fin.t.

(* Constructor notations *)
Notation "0" := Fin.F1 : fin_scope.
Notation "x +1" := (Fin.FS x) (at level 0) : fin_scope.

(* Index into a list *)
Definition index T (xs : list T) := Fin.t (length xs).
