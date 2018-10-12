From mathcomp.ssreflect
Require Import ssreflect.
From tlc.assert
Require Import scope type term.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Atoms for propositions *)
Definition atom {C} := @term C Bool.

Bind Scope tlc_core_scope with atom.
