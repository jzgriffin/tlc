From mathcomp.ssreflect
Require Import ssreflect seq.
From tlc.assert
Require Import prop.
From tlc.logic
Require Import program sequent temporal.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Proof system for TLC *)
Section tlc.

  Reserved Notation "X |- p"
    (at level 80, no associativity).

  Inductive tlc {C} : seq (@prop C) -> @prop C -> Prop :=
  | TProgram X p :
    X |-p C, p ->
    X |- p
  | TSequent X p :
    X |-s C, p ->
    X |- p
  | TTemporal X p :
    X |-t C, p ->
    X |- p
  where "X |- p" := (tlc X p).

End tlc.

Notation "X |- C , p" := (@tlc C X p)
  (at level 80, no associativity).

Lemma TProgram' {C} X p : X |- C, p -> X |-p C, p.
Proof.
Admitted. (* TODO *)

Lemma TSequent' {C} X p : X |- C, p -> X |-s C, p.
Proof.
Admitted. (* TODO *)

Lemma TTemporal' {C} X p : X |- C, p -> X |-t C, p.
Proof.
Admitted. (* TODO *)
