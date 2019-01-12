Require Import TLC.Concrete.Interface.
Require Import TLC.Parameters.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section fair_loss_link.

  Variable P : parameters.

  (* Input request type for the fair-loss link *)
  Inductive fll_request : Type :=
  | FLLSend (n : node P) (m : message P).

  (* Output indication type for the fair-loss link *)
  Inductive fll_indication : Type :=
  | FLLDeliver (n : node P) (m : message P).

  (* Interface for the fair-loss link *)
  Definition fll_interface : interface := (fll_request, fll_indication).

End fair_loss_link.
