From mathcomp.ssreflect
Require Import ssreflect eqtype ssrbool seq.
From tlc.assert
Require Import all_assert.
From tlc.comp
Require Import comp.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section sequent.

  Import AssertNotations.

  Variable node : eqType.
  Variable IR : eqType.
  Variable OI : eqType.
  Variable scs : subcomps.

  Reserved Notation "X |- c , A" (at level 80, no associativity).
  Inductive concludes (c : @comp node IR OI scs) :
    seq assertion -> assertion -> Prop :=
  | ConcludesAxiom A :
    [:: A] |- c, A
  | ConcludesThin X A A' :
    X |- c, A' ->
    A :: X |- c, A'
  | ConcludesContraction X A A' :
    A :: A :: X |- c, A' ->
    A :: X |- c, A'
  | ConcludesExchange X A A' A'' :
    A :: A' :: X |- c, A'' ->
    A' :: A :: X |- c, A''
  | ConcludesCut X A A' :
    X |- c, A ->
    A :: X |- c, A' ->
    X |- c, A'
  | ConcludesNegL X A A' :
    X |- c, A ->
    (~A)%A :: X |- c, A'
  | ConcludesNegR X A :
    A :: X |- c, Afalse ->
    X |- c, (~A)%A
  | ConcludesConjL X A A' A'' :
    A :: A' :: X |- c, A'' ->
    (A /\ A')%A :: X |- c, A''
  | ConcludesConjR X A A' :
    X |- c, A ->
    X |- c, A' ->
    X |- c, (A /\ A')%A
  | ConcludesDisjL X A A' A'' :
    A :: X |- c, A'' ->
    A' :: X |- c, A'' ->
    (A \/ A')%A :: X |- c, A''
  | ConcludesDisjRL X A A' :
    X |- c, A ->
    X |- c, (A \/ A')%A
  | ConcludesDisjRR X A A' :
    X |- c, A' ->
    X |- c, (A \/ A')%A
  | ConcludesImplL X A A' A'' :
    X |- c, A ->
    A' :: X |- c, A'' ->
    (A -> A')%A :: X |- c, A''
  | ConcludesImplR X A A' :
    A :: X |- c, A' ->
    X |- c, (A -> A')%A
  | ConcludesUnivL X A A' x x' :
    var_subst x (Tvar x') A :: X |- c, A' ->
    (univ: x, A)%A :: X |- c, A'
  | ConcludesUnivR X A x x' :
    free_var x' A ->
    X |- c, var_subst x (Tvar x') A ->
    X |- c, (univ: x, A)%A
  | ConcludesExistL X A A' x x' :
    free_var x' A ->
    var_subst x (Tvar x') A :: X |- c, A' ->
    (exis: x, A)%A :: X |- c, A'
  | ConcludesExistR X A x x' :
    X |- c, var_subst x (Tvar x') A ->
    X |- c, (exis: x, A)%A
  where "X |- c , A" := (concludes c X A).

End sequent.

Notation "X |- c , A" :=
  (concludes c X A)
  (at level 80, no associativity).
