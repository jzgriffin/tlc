From mathcomp.ssreflect
Require Import ssreflect seq.
From tlc.comp
Require Import all_comp.
From tlc.assert
Require Import all_assert.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Sequent logic for the assertion language *)
Section sequent.

  Reserved Notation "X |- A"
    (at level 80, no associativity).

  Inductive sequent {C : component} : seq (@prop C) -> @prop C -> Prop :=
  | SAxiom A :
    [:: A] |- A
  | SThin X A A' :
    X |- A' ->
    A :: X |- A'
  | SContraction X A A' :
    A :: A :: X |- A' ->
    A :: X |- A'
  | SExchange X A A' A'' :
    A :: A' :: X |- A'' ->
    A' :: A :: X |- A''
  | SCut X A A' :
    X |- A ->
    A :: X |- A' ->
    X |- A'
  | SNegL X A A' :
    X |- A ->
    (~A)%tlc :: X |- A'
  | SNegR X A :
    A :: X |- Atom TLC.false ->
    X |- (~A)%tlc
  | SConjL X A A' A'' :
    A :: A' :: X |- A'' ->
    (A /\ A')%tlc :: X |- A''
  | SConjR X A A' :
    X |- A ->
    X |- A' ->
    X |- (A /\ A')%tlc
  | SDisjL X A A' A'' :
    A :: X |- A'' ->
    A' :: X |- A'' ->
    (A \/ A')%tlc :: X |- A''
  | SDisjRL X A A' :
    X |- A ->
    X |- (A \/ A')%tlc
  | SDisjRR X A A' :
    X |- A' ->
    X |- (A \/ A')%tlc
  | SImplL X A A' A'' :
    X |- A ->
    A' :: X |- A'' ->
    (A -> A')%tlc :: X |- A''
  | SImplR X A A' :
    A :: X |- A' ->
    X |- (A -> A')%tlc
  (*
  | SUnivL X A A' x x' :
    var_subst x (Tvar x') A :: X A' ->
    (always: x, A)%tlc :: X A'
  | SUnivR X A x x' :
    free_var x' A ->
    X var_subst x (Tvar x') A ->
    X (always: x, A)%tlc
  | SExistL X A A' x x' :
    free_var x' A ->
    var_subst x (Tvar x') A :: X A' ->
    (exists: x, A)%tlc :: X A'
  | SExistR X A x x' :
    X var_subst x (Tvar x') A ->
    X (exists: x, A)%tlc
  *)
  where "X |- A" := (sequent X A).

End sequent.

Notation "X |-s C , A" :=
  (@sequent C X A)
  (at level 80, no associativity).
