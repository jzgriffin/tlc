From mathcomp.ssreflect
Require Import ssreflect eqtype ssrbool seq.
From tlc.comp
Require Import component.
From tlc.assert
Require Import all_assert.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Basic rules of sequent logic *)
Section sequent.

  Reserved Notation "X |- p"
    (at level 80, no associativity).

  Inductive sequent {C : component} : seq (@prop C) -> @prop C -> Prop :=

  (* Axiom/assumption *)
  | SAxiom p :
    [:: p] |- p

  (* Assumption modification *)
  | SThin X p q :
    X |- q ->
    p :: X |- q
  | SContraction X p q :
    p :: p :: X |- q ->
    p :: X |- q
  | SExchange X p q r :
    p :: q :: X |- r ->
    q :: p :: X |- r
  | SCut X p q :
    X |- p ->
    p :: X |- q ->
    X |- q

  (* Negation *)
  | SNotL X p q :
    X |- p ->
    (~p)%tlc :: X |- q
  | SNotR X p :
    p :: X |- False' ->
    X |- (~p)%tlc

  (* Disjunction *)
  | SOrL X p q r :
    p :: X |- r ->
    q :: X |- r ->
    (p \/ q)%tlc :: X |- r
  | SOrRL X p q :
    X |- p ->
    X |- (p \/ q)%tlc
  | SOrRR X p q :
    X |- q ->
    X |- (p \/ q)%tlc

  (* Conjunction *)
  | SAndL X p q r :
    p :: q :: X |- r ->
    (p /\ q)%tlc :: X |- r
  | SAndR X p q :
    X |- p ->
    X |- q ->
    X |- (p /\ q)%tlc

  (* Implication *)
  | SIfL X p q r :
    X |- p ->
    q :: X |- r ->
    (p -> q)%tlc :: X |- r
  | SIfR X p q :
    p :: X |- q ->
    X |- (p -> q)%tlc

  (* Universal quantification *)
  | SForallL X p q t (x : rigid_var t) :
    x \in prop_free_vars p t ->
    p :: X |- q ->
    (forall: x, p)%tlc :: X |- q
  | SForallR X p t (x : rigid_var t) :
    x \in prop_free_vars p t ->
    X |- p ->
    X |- (forall: x, p)%tlc

  (* Existential quantification *)
  | SExistsL X p q t (x : rigid_var t) :
    x \in prop_free_vars p t ->
    p :: X |- q ->
    (exists: x, p)%tlc :: X |- q
  | SExistsR X p t (x : rigid_var t) :
    x \in prop_free_vars p t ->
    X |- p ->
    X |- (exists: x, p)%tlc

  where "X |- p" := (sequent X p).

End sequent.

Notation "X |-s C , p" := (@sequent C X p)
  (at level 80, no associativity).
