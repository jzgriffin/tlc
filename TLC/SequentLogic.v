Require Import Coq.Lists.List.
Require Import TLC.ProgramLogic.
Require Import TLC.TemporalLogic.
Require Import TLC.Term.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Rules of sequent logic *)
Section sequent.

  Import ListNotations.

  Reserved Notation "X |- A"
    (at level 80, no associativity).

  Inductive sequent_logic {C} : list (term C Prop) -> term C Prop -> Prop :=

  (* Sub-logics *)
  | SequentTemporal X A :
    X |-t C, A ->
    X |- A
  | SequentProgram X A :
    X |-p C, A ->
    X |- A

  (* Axiom/assumption *)
  | SequentAxiom A :
    [A] |- A

  (* Assumption modification *)
  | SequentThin X A A' :
    X |- A' ->
    A :: X |- A'
  | SequentContraction X A A' :
    A :: A :: X |- A' ->
    A :: X |- A'
  | SequentExchange X A A' A'' :
    A :: A' :: X |- A'' ->
    A' :: A :: X |- A''
  | SequentCut X A A' :
    X |- A ->
    A :: X |- A' ->
    X |- A'

  (* Negation *)
  | SequentNotL X A A' :
    X |- A ->
    (~A)%tlc :: X |- A'
  | SequentNotR X A :
    A :: X |- ^False ->
    X |- ~A

  (* Conjunction *)
  | SequentAndL X A A' A'' :
    A :: A' :: X |- A'' ->
    (A /\ A')%tlc :: X |- A''
  | SequentAndR X A A' :
    X |- A ->
    X |- A' ->
    X |- (A /\ A')

  (* Disjunction *)
  | SequentOrL X A A' A'' :
    A :: X |- A'' ->
    A' :: X |- A'' ->
    (A \/ A')%tlc :: X |- A''
  | SequentOrRL X A A' :
    X |- A ->
    X |- (A \/ A')
  | SequentOrRR X A A' :
    X |- A' ->
    X |- (A \/ A')

  (* Implication *)
  | SequentIfL X A A' A'' :
    X |- A ->
    A' :: X |- A'' ->
    (A -> A')%tlc :: X |- A''
  | SequentIfR X A A' :
    A :: X |- A' ->
    X |- (A -> A')

  (* Universal quantification *)
  | SequentForAllL X T (x : T) A A' :
    A x :: X |- A' ->
    ForAll A :: X |- A'
  | SequentForAllR X T (x : T) A :
    X |- A x ->
    X |- ForAll A

  (* Existential quantification *)
  | SequentExistsL X T (x : T) A A' :
    A x :: X |- A' ->
    Exists A :: X |- A'
  | SequentExistsR X T (x : T) A :
    X |- A x ->
    X |- Exists A

  where "X |- A" := (sequent_logic X A).

End sequent.

Arguments sequent_logic : clear implicits.

Coercion SequentTemporal : temporal_logic >-> sequent_logic.
Coercion SequentProgram : program_logic >-> sequent_logic.

Notation "X |- C , A" := (sequent_logic C X A)
  (at level 80, no associativity).
