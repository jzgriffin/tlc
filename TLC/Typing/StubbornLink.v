Require Import TLC.Typing.Component.
Require Import TLC.Typing.FairLossLink.
Require Import TLC.Typing.Type.
Require Import Coq.Lists.List.
Require TLC.Syntax.StubbornLink.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module SSL := TLC.Syntax.StubbornLink.

Section sl_component.

  Import ListNotations.

  Definition sl_component P : component P :=
    @Component _ (SSL.sl_component P)
      TSLRequest
      TSLIndication
      [fll_interface]
      TSLState.

End sl_component.
