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
    |-p C, p ->
    X |- p
  | TSequent X p :
    X |-s C, p ->
    X |- p
  | TTemporal X p :
    |-t C, p ->
    X |- p
  where "X |- p" := (tlc X p).

End tlc.

Notation "X |- C , p" := (@tlc C X p)
  (at level 80, no associativity).
