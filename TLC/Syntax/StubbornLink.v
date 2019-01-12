Require Import TLC.Syntax.Component.
Require Import TLC.Syntax.Constant.
Require TLC.Concrete.StubbornLink.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module CSL := TLC.Concrete.StubbornLink.

Definition sl_component P :=
  Component (CSL.sl_component P)
    CSLInitialize
    CSLRequest
    CSLIndication
    CSLPeriodic.
