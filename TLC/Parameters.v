Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Logic-wide parameters *)
Record parameters : Type :=
  Parameters {
    node : Type;
    message : Type;
  }.
