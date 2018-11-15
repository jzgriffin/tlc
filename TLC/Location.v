Require Import TLC.Component.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* TODO: This type should depend on the stack *)
Definition location (C : component) : Type := list nat.
