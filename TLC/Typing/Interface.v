Require Import TLC.Typing.Type.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Type of external typing interfaces of components *)
Definition interface : Type := type * type.
Definition interfaces := list interface.
