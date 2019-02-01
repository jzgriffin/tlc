Require Import mathcomp.ssreflect.seq.
Require Import mathcomp.ssreflect.ssreflect.
Require Import tlc.assert.all_assert.
Require Import tlc.compute.all_compute.
Require Import tlc.logic.context.
Require Import tlc.utility.result.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Reserved Notation "C |- A" (at level 70, no associativity).

(* Basic syntactic rules and axioms *)
Inductive derives : context -> assertion -> Prop :=
(* Assertion logic *)
| DATrue C :
  C |- CTrue
| DAGoal C e e' :
  evaluate (context_environment C) e = Value e' ->
  C |- e' ->
  C |- e
| DAHypothesis C e e' A :
  evaluate (context_environment C) e = Value e' ->
  {A: #e'} :: C |- A ->
  {A: #e} :: C |- A
(* Sequent logic *)
| DSAxiom C A :
  A :: C |- A
| DSThin C A1 A2 :
  C |- A2 ->
  A1 :: C |- A2
| DSContraction C A1 A2 :
  A1 :: A1 :: C |- A2 ->
  A1 :: C |- A2
| DSExchange C A1 A2 A3 :
  (A1 :: A2 :: C) |- A3 ->
  (A2 :: A1 :: C) |- A3
| DSCut C A1 A2 :
  C |- A1 ->
  A1 :: C |- A2 ->
  C |- A2
| DSNotL C A1 A2 :
  C |- A1 ->
  {A: ~A1} :: C |- A2
| DSNotR C A :
  A :: C |- CFalse ->
  C |- {A: ~A}
| DSOrL C A1 A2 A3 :
  A1 :: C |- A3 ->
  A2 :: C |- A3 ->
  {A: A1 \/ A2} :: C |- A3
| DSOrRL C A1 A2 :
  C |- A1 ->
  C |- {A: A1 \/ A2}
| DSOrRR C A1 A2 :
  C |- A2 ->
  C |- {A: A1 \/ A2}
| DSAndL C A1 A2 A3 :
  A1 :: A2 :: C |- A3 ->
  {A: A1 /\ A2} :: C |- A3
| DSAndR C A1 A2 :
  C |- A1 ->
  C |- A2 ->
  C |- {A: A1 /\ A2}
| DSIfL C A1 A2 A3 :
  C |- A1 ->
  A2 :: C |- A3 ->
  {A: A1 -> A2} :: C |- A3
| DSIfR C A1 A2 :
  A1 :: C |- A2 ->
  C |- {A: A1 -> A2}
where "C |- A" := (derives C A).
