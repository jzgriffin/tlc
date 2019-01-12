Require Import TLC.Typing.ComponentProofs.
Require Import TLC.Typing.Expression.
Require Import TLC.Typing.StubbornLink.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition sl_component_proofs P :=
  @ComponentProofs _ (sl_component P)
    TECSLInitialize
    TECSLRequest
    TECSLIndication
    TECSLPeriodic.
