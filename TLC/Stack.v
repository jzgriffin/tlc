Require Import Coq.Vectors.Vector.
Require Import TLC.Component.
Require Import TLC.FairLossLink.
Require Import TLC.TupleMap.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section stack.

  Variable node : Type.
  Variable message : Type.

  Inductive stack : Type -> Type -> Type :=
  | FairLossLink : stack (request_fl node message) (indication_fl node message)
  | ComponentStack (C : component) :
    tuple_map (fun i => stack (fst i) (snd i))
      (Vector.to_list (projT2 (sub_interfaces C))) ->
    stack (ir_event C) (oi_event C).

End stack.
