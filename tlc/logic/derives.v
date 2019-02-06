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
(* Temporal logic future *)
| DT1 C A :
  C |- {A: always A -> A}
| DT2 C A :
  C |- {A: (next ~A) <=> ~next A}
| DT3 C Al Ar :
  C |- {A: (next (Al -> Ar)) <=> (next Al -> next Ar)}
| DT4 C Al Ar :
  C |- {A: (always (Al -> Ar)) =>> (always Al -> always Ar)}
| DT5 C A :
  C |- {A: (always A) -> always next A}
| DT6 C A :
  C |- {A: (A =>> next A) -> (A =>> always A)}
| DT7 C Al Ar :
  C |- {A: (Al unless Ar) <=> (Ar \/ (Al /\ next (Al unless Ar)))}
| DT8 C Al Ar :
  C |- {A: (always Al) =>> Al unless Ar}
(* Temporal logic past *)
| DT9 C A :
  C |- {A: previous A =>> previous^ A}
| DT10 C Al Ar :
  C |- {A: previous^ (Al -> Ar) <=> (previous^ Al -> previous^ Ar)}
| DT11 C Al Ar :
  C |- {A: alwaysp (Al -> Ar) =>> (alwaysp Al -> alwaysp Ar)}
| DT12 C A :
  C |- {A: always A -> always previous^ A}
| DT13 C A :
  C |- {A: (A =>> previous^ A) -> (A =>> alwaysp A)}
| DT14 C Al Ar :
  C |- {A: (Al backto Ar) <=> (Ar \/ (Al /\ previous^ (Al backto Ar)))}
| DT15 C :
  C |- previous^ false
(* Temporal logic mixed *)
| DT16 C A :
  C |- {A: A =>> next previous A}
| DT17 C A :
  C |- {A: A =>> previous^ next A}
(* Temporal logic rules *)
| DTGeneralization C A :
  C |- A ->
  C |- {A: always A}
| DT18 C v A :
  C |- {A: (forall: v, next A) <=> (next forall: v, A)}
where "C |- A" := (derives C A).

Hint Constructors derives.

(* Rewriting *)
Fixpoint rewrite_entails C Ae Ae' (H : C |- {A: Ae =>> Ae'}) A :=
  if A == Ae then Ae' else
  match A with
  | APredicate _ => A
  | ANot A => ANot (rewrite_entails H A)
  | AOr Al Ar => AOr (rewrite_entails H Al) (rewrite_entails H Ar)
  | AForAll v A => AForAll v (rewrite_entails H A)
  | AUntil' Al Ar => AUntil' (rewrite_entails H Al) (rewrite_entails H Ar)
  | ASince' Al Ar => ASince' (rewrite_entails H Al) (rewrite_entails H Ar)
  | ASelf A => ASelf (rewrite_entails H A)
  end.

Lemma rewrite_entails_correct C Ae Ae' (H : C |- {A: Ae =>> Ae'}) A :
  C |- (rewrite_entails H A) -> C |- A.
Proof.
Admitted. (* TODO *)

Ltac rewrite_entails H := apply rewrite_entails_correct with (H := H).

Definition congruent_left_right C Al Ar (H : C |- {A: Al <=> Ar}) :
  C |- {A: Al =>> Ar}.
Proof.
  apply DSCut with (A1 := {A: Al <=> Ar}); first by [].
  apply DSAndL, DSAxiom.
Defined.

Definition rewrite_congruent_left_right C Ae Ae' (H : C |- {A: Ae <=> Ae'}) :=
  rewrite_entails (congruent_left_right H).

Ltac rewrite_congruent_left_right H :=
  apply rewrite_entails_correct with (H := congruent_left_right H).

Definition congruent_right_left C Al Ar (H : C |- {A: Al <=> Ar}) :
  C |- {A: Ar =>> Al}.
Proof.
  apply DSCut with (A1 := {A: Al <=> Ar}); first by [].
  apply DSAndL, DSExchange, DSAxiom.
Defined.

Definition rewrite_congruent_right_left C Ae Ae' (H : C |- {A: Ae <=> Ae'}) :=
  rewrite_entails (congruent_right_left H).

Ltac rewrite_congruent_right_left H:=
  apply rewrite_entails_correct with (H := congruent_right_left H).

(* Derived rules and lemmas *)

Lemma Lemma76 C A1 A2 :
  C |- {A: A1 =>> A2} ->
  C |- {A: always A1} ->
  C |- {A: always A2}.
Proof.
Admitted. (* TODO *)

Lemma Lemma77 C A1 A2 A3 :
  C |- {A: A1 =>> A2} ->
  C |- {A: A2 =>> A3} ->
  C |- {A: A1 =>> A3}.
Proof.
Admitted. (* TODO *)

Lemma Lemma78_1 C A1 A2 :
  C |- {A: A1 =>> A2} ->
  C |- {A: (next A1) =>> next A2}.
Proof.
Admitted. (* TODO *)

Lemma Lemma78_2 C A1 A2 :
  C |- {A: A1 <=> A2} ->
  C |- {A: (next A1) <=> (next A2)}.
Proof.
Admitted. (* TODO *)

Lemma Lemma79 C A :
  C |- {A: A =>> next A} ->
  C |- {A: A =>> always A}.
Proof.
Admitted. (* TODO *)

Lemma Lemma80 C A :
  C |- {A: always A =>> A}.
Proof.
Admitted. (* TODO *)

Lemma Lemma81 C A1 A2 :
  C |- {A: always (A1 /\ A2) <=> always A1 /\ always A2}.
Proof.
Admitted. (* TODO *)

Lemma Lemma83_1 C A :
  C |- {A: eventuallyp A <=> eventuallyp eventuallyp A}.
Proof.
Admitted. (* TODO *)

Lemma Lemma83_2 C A :
  C |- {A: eventuallyp^ eventuallyp^ A =>> eventuallyp^ A}.
Proof.
Admitted. (* TODO *)

Lemma Lemma83_3 C A :
  C |- {A: eventuallyp eventuallyp^ A =>> eventuallyp^ A}.
Proof.
Admitted. (* TODO *)

Lemma Lemma83_4 C A :
  C |- {A: eventuallyp^ eventuallyp A =>> eventuallyp^ A}.
Proof.
Admitted. (* TODO *)

Lemma Lemma84 C A :
  C |- {A: eventually A <=> eventually eventually A}.
Proof.
Admitted. (* TODO *)

Lemma Lemma85 C A1 A2 A3 :
  C |- {A: A1 =>> eventuallyp A2} ->
  C |- {A: A2 =>> eventuallyp A3} ->
  C |- {A: A1 =>> eventuallyp A3}.
Proof.
Admitted. (* TODO *)

Lemma Lemma86 C A1 A2 A3 :
  C |- {A: A1 =>> eventually A2} ->
  C |- {A: A2 =>> eventually A3} ->
  C |- {A: A1 =>> eventually A3}.
Proof.
Admitted. (* TODO *)

Lemma Lemma87 C A :
  C |- {A: A =>> eventuallyp A}.
Proof.
Admitted. (* TODO *)

Lemma Lemma90 C A :
  C |- {A: (self ~A) <=> ~self A}.
Proof.
Admitted. (* TODO *)

Lemma Lemma91 C A :
  C |- {A: A -> previous^ next A}.
Proof.
Admitted. (* TODO *)

Lemma Lemma94 C A1 A2 :
  C |- {A: ((A1 =>> A2) /\ A1) -> A2}.
Proof.
Admitted. (* TODO *)

Lemma Lemma96_1 C A1 A2 A3 :
  C |- {A: (A1 =>> eventually A2) /\ (A2 =>> A3) -> A1 =>> eventually A3}.
Proof.
Admitted. (* TODO *)

Lemma Lemma96_2 C A1 A2 A3 :
  C |- {A: (A1 =>> eventuallyp A2) /\ (A2 =>> A3) -> A1 =>> eventuallyp A3}.
Proof.
Admitted. (* TODO *)

Lemma Lemma96_3 C A1 A2 A3 :
  C |- {A: (A1 =>> eventuallyp^ A2) /\ (A2 =>> A3) -> A1 =>> eventuallyp^ A3}.
Proof.
Admitted. (* TODO *)

Lemma Lemma97 C A1 A2 A3 :
  C |- {A: (A1 =>> always A2) /\ (A2 =>> A3) -> A1 =>> always A3}.
Proof.
Admitted. (* TODO *)

Lemma Lemma98_1 C A :
  C |- {A: eventuallyp always A =>> A}.
Proof.
Admitted. (* TODO *)

Lemma Lemma98_2 C A :
  C |- {A: eventuallyp always^ A =>> A}.
Proof.
Admitted. (* TODO *)

Lemma Lemma98_3 C A :
  C |- {A: eventuallyp^ always A =>> A}.
Proof.
Admitted. (* TODO *)

Lemma Lemma100 C A :
  C |- {A: A -> (alwaysp^ (A =>> self A) =>> A)}.
Proof.
Admitted. (* TODO *)

Lemma Lemma102_1 C A1 A2 :
  C |- {A: (eventually A1 /\ eventually A2) =>>
    ((A1 <-> A2) \/
      eventually (A1 /\ eventually A2) \/
      eventually (A2 /\ eventually A1))}.
Proof.
Admitted. (* TODO *)

Lemma Lemma102_2 C A1 A2 :
  C |- {A: (eventuallyp A1 /\ eventuallyp A2) =>>
    ((A1 <-> A2) \/
      eventuallyp (A1 /\ eventuallyp A2) \/
      eventuallyp (A2 /\ eventuallyp A1))}.
Proof.
Admitted. (* TODO *)

Lemma Lemma102_3 C A1 A2 :
  C |- {A: (eventuallyp A1 /\ eventually A2) =>>
      eventuallyp (A1 /\ eventually A2)}.
Proof.
Admitted. (* TODO *)

Lemma Lemma103_1 C A :
  C |- {A: (eventually A /\ always^ ~A) =>> A}.
Proof.
Admitted. (* TODO *)

Lemma Lemma103_2 C A :
  C |- {A: (eventuallyp A /\ alwaysp^ ~A) =>> A}.
Proof.
Admitted. (* TODO *)

Lemma Lemma104 C A :
  C |- {A: eventuallyp A =>> always eventuallyp A}.
Proof.
Admitted. (* TODO *)

Lemma Lemma105_1 C A :
  C |- {A: (A =>> always^ ~A) -> (A =>> alwaysp^ ~A)}.
Proof.
Admitted. (* TODO *)

Lemma Lemma105_2 C A :
  C |- {A: (A =>> alwaysp^ ~A) -> (A =>> always^ ~A)}.
Proof.
Admitted. (* TODO *)

Lemma Lemma106 C A1 A2 :
  C |- {A: (A1 =>> eventuallyp (A1 =>> A2)) -> (A1 =>> A2)}.
Proof.
Admitted. (* TODO *)

Lemma Lemma107 C A :
  C |- {A: (alwaysp^ A =>> A) -> always A}.
Proof.
Admitted. (* TODO *)

Lemma Lemma108 C A1 A2 :
  C |- {A: ((alwaysp^ A1 /\ alwaysp^ A2) =>>
    (A1 /\ A2)) -> always (A1 /\ A2)}.
Proof.
Admitted. (* TODO *)

Lemma Lemma109_1 C A :
  C |- {A: eventuallyp eventually A <=> eventually A \/ eventuallyp A}.
Proof.
Admitted. (* TODO *)

Lemma Lemma109_2 C A :
  C |- {A: eventuallyp^ eventually A =>> eventually A \/ eventuallyp A}.
Proof.
Admitted. (* TODO *)

Lemma Lemma109_3 C A :
  C |- {A: eventually eventuallyp A =>> eventually A \/ eventuallyp A}.
Proof.
Admitted. (* TODO *)

Lemma Lemma109_4 C A :
  C |- {A: eventually eventuallyp^ A =>> eventually A \/ eventuallyp A}.
Proof.
Admitted. (* TODO *)

Lemma Lemma109_5 C A :
  C |- {A: eventuallyp^ eventually^ A =>> eventually A \/ eventuallyp A}.
Proof.
Admitted. (* TODO *)

Lemma Lemma111 C A :
  C |- {A: (eventuallyp A) <=> self eventuallyp^ A}.
Proof.
Admitted. (* TODO *)

Lemma Lemma112 C A1 A2 :
  C |- {A: (eventually A1 /\ always A2) =>> eventually (A1 /\ always A2)}.
Proof.
Admitted. (* TODO *)

Lemma Lemma114 C A :
  C |- {A: (~eventuallyp^ A) =>> alwaysp^ ~A}.
Proof.
Admitted. (* TODO *)

Lemma Lemma115 C A :
  C |- {A: (alwaysp^ A) <=> alwaysp previous^ A}.
Proof.
Admitted. (* TODO *)

Lemma Lemma116 C A1 A2 :
  C |- {A: (A1 /\ eventuallyp^ A2) =>> eventuallyp^ (A2 /\ eventually A1)}.
Proof.
Admitted. (* TODO *)

Lemma Lemma117 C A :
  C |- {A: (alwaysp A /\ always A) =>>
    alwaysp alwaysp^ A /\ always alwaysp^ A}.
Proof.
Admitted. (* TODO *)

Lemma Lemma118 C A :
  C |- {A: (eventuallyp^ self A) <=> eventuallyp A}.
Proof.
Admitted. (* TODO *)
