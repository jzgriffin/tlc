Require Import TLC.Logic.Derives.
Require Import TLC.Parameters.
Require Import TLC.Syntax.Constant.
Require Import TLC.Syntax.Expression.
Require Import TLC.Syntax.Formula.
Require Import TLC.Syntax.Predicate.
Require Import TLC.Syntax.StubbornLink.
Require Import Coq.Lists.List.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section stubborn_link.

  Variable P : parameters.

  (* Stubborn delivery *)
  Lemma SL_1 n n' m : nil |- (
    PCorrect n /\ PCorrect n' ->
      ((when-on[n] when[]-> CSLSend <- n' <- m) =>>
        (always eventually when-on[n'] when[]<- CSLDeliver <- n <- m))).
  Proof.
    set (C := sl_component P).
  Admitted. (* TODO *)

  (* No-forge *)
  Lemma SL_2 n n' m : nil |- (
    (when-on[n] when[]<- CSLDeliver <- n' <- m) <~
      (when-on[n'] when[]-> CSLSend <- n <- m)).
  Proof.
    set (C := sl_component P).
  Admitted. (* TODO *)

End stubborn_link.
