Require Import mathcomp.ssreflect.eqtype.
Require Import mathcomp.ssreflect.seq.
Require Import mathcomp.ssreflect.ssrbool.
Require Import mathcomp.ssreflect.ssreflect.
Require Import tlc.semantics.all_semantics.
Require Import tlc.syntax.all_syntax.
Require Import tlc.logic.context.
Require Import tlc.utility.result.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Basic syntactic rules and axioms *)
Reserved Notation "C |- A" (at level 70, no associativity).
Inductive derives : context -> assertion -> Prop :=
(* Assertion logic *)
| DATrue C :
  C |- CTrue
| DAHypothesis C t t' A :
  [[ t[t/context_environment C] ]] = Success t' ->
  {A: #t'} :: C |- A ->
  {A: #t} :: C |- A
| DAConclusion C t t' :
  [[ t[t/context_environment C] ]] = Success t' ->
  C |- t' ->
  C |- t
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
| DSForAllL C v t A1 A2 :
  A1[A/ [:: (v, t)] ] :: C |- A2 ->
  {A: forall: v, A1} :: C |- A2
| DSForAllR C v t A :
  C |- A[A/ [:: (v, t)] ] ->
  C |- {A: forall: v, A}
| DSExistsL C v t A1 A2 :
  A1[A/ [:: (v, t)] ] :: C |- A2 ->
  {A: exists: v, A1} :: C |- A2
| DSExistsR C v t A :
  C |- A[A/ [:: (v, t)] ] ->
  C |- {A: exists: v, A}
where "C |- A" := (derives C A).

Hint Constructors derives.
