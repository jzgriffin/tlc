Require Import TLC.Concrete.Component.
Require Import TLC.Concrete.FairLossLink.
Require Import TLC.Concrete.Interface.
Require Import TLC.Parameters.
Require Import TLC.Utility.HList.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section stack.

  Variable P : parameters.

  (* Type of stacks of components *)
  Inductive stack : interface -> Type :=
  | FairLossLink :
    stack (fll_interface P)
  | Stack (C : component P) :
    hlist stack (sub_interfaces C) ->
    stack (ir_event C, oi_event C).

End stack.
