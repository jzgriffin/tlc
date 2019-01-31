Require Import mathcomp.ssreflect.seq.
Require Import mathcomp.ssreflect.ssreflect.
Require Import tlc.assert.assertion.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Reserved Notation "Gamma |- A" (at level 70, no associativity).

(* Basic syntactic rules and axioms *)
Inductive derives : seq assertion -> assertion -> Prop :=
(* Sequent logic *)
| DSAxiom Gamma A :
  A :: Gamma |- A
| DSThin Gamma A1 A2 :
  Gamma |- A2 ->
  A1 :: Gamma |- A2
| DSContraction Gamma A1 A2 :
  A1 :: A1 :: Gamma |- A2 ->
  A1 :: Gamma |- A2
| DSExchange Gamma A1 A2 A3 :
  (A1 :: A2 :: Gamma) |- A3 ->
  (A2 :: A1 :: Gamma) |- A3
| DSCut Gamma A1 A2 :
  Gamma |- A1 ->
  A1 :: Gamma |- A2 ->
  Gamma |- A2
| DSNotL Gamma A1 A2 :
  Gamma |- A1 ->
  {A: ~A1} :: Gamma |- A2
| DSNotR Gamma A :
  A :: Gamma |- AFalse ->
  Gamma |- {A: ~A}
| DSOrL Gamma A1 A2 A3 :
  A1 :: Gamma |- A3 ->
  A2 :: Gamma |- A3 ->
  {A: A1 \/ A2} :: Gamma |- A3
| DSOrRL Gamma A1 A2 :
  Gamma |- A1 ->
  Gamma |- {A: A1 \/ A2}
| DSOrRR Gamma A1 A2 :
  Gamma |- A2 ->
  Gamma |- {A: A1 \/ A2}
| DSAndL Gamma A1 A2 A3 :
  A1 :: A2 :: Gamma |- A3 ->
  {A: A1 /\ A2} :: Gamma |- A3
| DSAndR Gamma A1 A2 :
  Gamma |- A1 ->
  Gamma |- A2 ->
  Gamma |- {A: A1 /\ A2}
| DSIfL Gamma A1 A2 A3 :
  Gamma |- A1 ->
  A2 :: Gamma |- A3 ->
  {A: A1 -> A2} :: Gamma |- A3
| DSIfR Gamma A1 A2 :
  A1 :: Gamma |- A2 ->
  Gamma |- {A: A1 -> A2}
where "Gamma |- A" := (derives Gamma A).
