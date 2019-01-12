Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Type of external concrete interfaces of components *)
Definition interface : Type := Type * Type.
Definition interfaces := list interface.
