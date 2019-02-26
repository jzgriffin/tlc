Require Import mathcomp.ssreflect.ssreflect.
Require Import tlc.component.component.
Require Import tlc.logic.derives.
Require Import tlc.syntax.all_syntax.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Derived temporal rules and lemmas *)

Lemma DTL76 C Gamma A1 A2 :
  Gamma |- C, {A: A1 =>> A2} ->
  Gamma |- C, {A: always A1} ->
  Gamma |- C, {A: always A2}.
Proof.
Admitted. (* TODO *)

Lemma DTL77 C Gamma A1 A2 A3 :
  Gamma |- C, {A: A1 =>> A2} ->
  Gamma |- C, {A: A2 =>> A3} ->
  Gamma |- C, {A: A1 =>> A3}.
Proof.
Admitted. (* TODO *)

Lemma DTL78_1 C Gamma A1 A2 :
  Gamma |- C, {A: A1 =>> A2} ->
  Gamma |- C, {A: next A1 =>> next A2}.
Proof.
Admitted. (* TODO *)

Lemma DTL78_2 C Gamma A1 A2 :
  Gamma |- C, {A: A1 <=> A2} ->
  Gamma |- C, {A: next A1 <=> next A2}.
Proof.
Admitted. (* TODO *)

Lemma DTL79 C Gamma A :
  Gamma |- C, {A: A =>> next A} ->
  Gamma |- C, {A: A =>> always A}.
Proof.
Admitted. (* TODO *)

Lemma DTL80 C Gamma A :
  Gamma |- C, {A: always A =>> A}.
Proof.
Admitted. (* TODO *)

Lemma DTL81 C Gamma A1 A2 :
  Gamma |- C, {A: always (A1 /\ A2) <=> always A1 /\ always A2}.
Proof.
Admitted. (* TODO *)

Lemma DTL83_1 C Gamma A :
  Gamma |- C, {A: eventuallyp A <=> eventuallyp eventuallyp A}.
Proof.
Admitted. (* TODO *)

Lemma DTL83_2 C Gamma A :
  Gamma |- C, {A: eventuallyp^ eventuallyp^ A =>> eventuallyp^ A}.
Proof.
Admitted. (* TODO *)

Lemma DTL83_3 C Gamma A :
  Gamma |- C, {A: eventuallyp eventuallyp^ A =>> eventuallyp^ A}.
Proof.
Admitted. (* TODO *)

Lemma DTL83_4 C Gamma A :
  Gamma |- C, {A: eventuallyp^ eventuallyp A =>> eventuallyp^ A}.
Proof.
Admitted. (* TODO *)

Lemma DTL84 C Gamma A :
  Gamma |- C, {A: eventually A <=> eventually eventually A}.
Proof.
Admitted. (* TODO *)

Lemma DTL85 C Gamma A1 A2 A3 :
  Gamma |- C, {A: A1 =>> eventuallyp A2} ->
  Gamma |- C, {A: A2 =>> eventuallyp A3} ->
  Gamma |- C, {A: A1 =>> eventuallyp A3}.
Proof.
Admitted. (* TODO *)

Lemma DTL86 C Gamma A1 A2 A3 :
  Gamma |- C, {A: A1 =>> eventually A2} ->
  Gamma |- C, {A: A2 =>> eventually A3} ->
  Gamma |- C, {A: A1 =>> eventually A3}.
Proof.
Admitted. (* TODO *)

Lemma DTL87 C Gamma A :
  Gamma |- C, {A: A =>> eventuallyp A}.
Proof.
Admitted. (* TODO *)

Lemma DTL90 C Gamma A :
  Gamma |- C, {A: (self ~A) <=> ~self A}.
Proof.
Admitted. (* TODO *)

Lemma DTL91 C Gamma A :
  Gamma |- C, {A: A -> previous^ next A}.
Proof.
Admitted. (* TODO *)

Lemma DTL94 C Gamma A1 A2 :
  Gamma |- C, {A: (A1 =>> A2) /\ A1 -> A2}.
Proof.
Admitted. (* TODO *)

Lemma DTL96_1 C Gamma A1 A2 A3 :
  Gamma |- C, {A:
    (A1 =>> eventually A2) /\ (A2 =>> A3) ->
    A1 =>> eventually A3
  }.
Proof.
Admitted. (* TODO *)

Lemma DTL96_2 C Gamma A1 A2 A3 :
  Gamma |- C, {A:
    (A1 =>> eventuallyp A2) /\ (A2 =>> A3) ->
    A1 =>> eventuallyp A3
  }.
Proof.
Admitted. (* TODO *)

Lemma DTL96_3 C Gamma A1 A2 A3 :
  Gamma |- C, {A:
    (A1 =>> eventuallyp^ A2) /\ (A2 =>> A3) ->
    A1 =>> eventuallyp^ A3
  }.
Proof.
Admitted. (* TODO *)

Lemma DTL97 C Gamma A1 A2 A3 :
  Gamma |- C, {A: (A1 =>> always A2) /\ (A2 =>> A3) -> A1 =>> always A3}.
Proof.
Admitted. (* TODO *)

Lemma DTL98_1 C Gamma A :
  Gamma |- C, {A: eventuallyp always A =>> A}.
Proof.
Admitted. (* TODO *)

Lemma DTL98_2 C Gamma A :
  Gamma |- C, {A: eventuallyp always^ A =>> A}.
Proof.
Admitted. (* TODO *)

Lemma DTL98_3 C Gamma A :
  Gamma |- C, {A: eventuallyp^ always A =>> A}.
Proof.
Admitted. (* TODO *)

Lemma DTL100 C Gamma A :
  Gamma |- C, {A: A -> alwaysp^ (A =>> self A) =>> A}.
Proof.
Admitted. (* TODO *)

Lemma DTL102_1 C Gamma A1 A2 :
  Gamma |- C, {A:
    eventually A1 /\ eventually A2 =>>
    (A1 <-> A2) \/
      eventually (A1 /\ eventually A2) \/
      eventually (A2 /\ eventually A1)
  }.
Proof.
Admitted. (* TODO *)

Lemma DTL102_2 C Gamma A1 A2 :
  Gamma |- C, {A:
    eventuallyp A1 /\ eventuallyp A2 =>>
    (A1 <-> A2) \/
      eventuallyp (A1 /\ eventuallyp A2) \/
      eventuallyp (A2 /\ eventuallyp A1)
  }.
Proof.
Admitted. (* TODO *)

Lemma DTL102_3 C Gamma A1 A2 :
  Gamma |- C, {A:
    eventuallyp A1 /\ eventually A2 =>>
    eventuallyp (A1 /\ eventually A2)
  }.
Proof.
Admitted. (* TODO *)

Lemma DTL103_1 C Gamma A :
  Gamma |- C, {A: (eventually A /\ always^ ~A) =>> A}.
Proof.
Admitted. (* TODO *)

Lemma DTL103_2 C Gamma A :
  Gamma |- C, {A: (eventuallyp A /\ alwaysp^ ~A) =>> A}.
Proof.
Admitted. (* TODO *)

Lemma DTL104 C Gamma A :
  Gamma |- C, {A: eventuallyp A =>> always eventuallyp A}.
Proof.
Admitted. (* TODO *)

Lemma DTL105_1 C Gamma A :
  Gamma |- C, {A: (A =>> always^ ~A) -> A =>> alwaysp^ ~A}.
Proof.
Admitted. (* TODO *)

Lemma DTL105_2 C Gamma A :
  Gamma |- C, {A: (A =>> alwaysp^ ~A) -> A =>> always^ ~A}.
Proof.
Admitted. (* TODO *)

Lemma DTL106 C Gamma A1 A2 :
  Gamma |- C, {A: (A1 =>> eventuallyp (A1 =>> A2)) -> A1 =>> A2}.
Proof.
Admitted. (* TODO *)

Lemma DTL107 C Gamma A :
  Gamma |- C, {A: (alwaysp^ A =>> A) -> always A}.
Proof.
Admitted. (* TODO *)

Lemma DTL108 C Gamma A1 A2 :
  Gamma |- C, {A:
    (alwaysp^ A1 /\ alwaysp^ A2 =>> A1 /\ A2) -> always (A1 /\ A2)
  }.
Proof.
Admitted. (* TODO *)

Lemma DTL109_1 C Gamma A :
  Gamma |- C, {A:
    eventuallyp eventually A <=> eventually A \/ eventuallyp A
  }.
Proof.
Admitted. (* TODO *)

Lemma DTL109_2 C Gamma A :
  Gamma |- C, {A:
    eventuallyp^ eventually A =>> eventually A \/ eventuallyp A
  }.
Proof.
Admitted. (* TODO *)

Lemma DTL109_3 C Gamma A :
  Gamma |- C, {A:
    eventually eventuallyp A =>> eventually A \/ eventuallyp A
  }.
Proof.
Admitted. (* TODO *)

Lemma DTL109_4 C Gamma A :
  Gamma |- C, {A:
    eventually eventuallyp^ A =>> eventually A \/ eventuallyp A
  }.
Proof.
Admitted. (* TODO *)

Lemma DTL109_5 C Gamma A :
  Gamma |- C, {A:
    eventuallyp^ eventually^ A =>> eventually A \/ eventuallyp A
  }.
Proof.
Admitted. (* TODO *)

Lemma DTL111 C Gamma A :
  Gamma |- C, {A: eventuallyp A <=> self eventuallyp^ A}.
Proof.
Admitted. (* TODO *)

Lemma DTL112 C Gamma A1 A2 :
  Gamma |- C, {A:
    eventually A1 /\ always A2 =>> eventually (A1 /\ always A2)
  }.
Proof.
Admitted. (* TODO *)

Lemma DTL114 C Gamma A :
  Gamma |- C, {A: ~eventuallyp^ A =>> alwaysp^ ~A}.
Proof.
Admitted. (* TODO *)

Lemma DTL115 C Gamma A :
  Gamma |- C, {A: alwaysp^ A <=> alwaysp previous^ A}.
Proof.
Admitted. (* TODO *)

Lemma DTL116 C Gamma A1 A2 :
  Gamma |- C, {A:
    A1 /\ eventuallyp^ A2 =>>
    eventuallyp^ (A2 /\ eventually A1)
  }.
Proof.
Admitted. (* TODO *)

Lemma DTL117 C Gamma A :
  Gamma |- C, {A:
    alwaysp A /\ always A =>>
    alwaysp alwaysp^ A /\ always alwaysp^ A
  }.
Proof.
Admitted. (* TODO *)

Lemma DTL118 C Gamma A :
  Gamma |- C, {A: eventuallyp^ self A <=> eventuallyp A}.
Proof.
Admitted. (* TODO *)

Lemma DTL119 C Gamma A :
  Gamma |- C, {A: always^ always A <=> always^ A}.
Proof.
Admitted. (* TODO *)

Lemma DTL120_1 C Gamma A :
  Gamma |- C, {A: eventually A <=> eventually eventually A}.
Proof.
Admitted. (* TODO *)

Lemma DTL120_2 C Gamma A :
  Gamma |- C, {A: eventually^ eventually^ A =>> eventually^ A}.
Proof.
Admitted. (* TODO *)

Lemma DTL120_3 C Gamma A :
  Gamma |- C, {A: eventually eventually^ A =>> eventually^ A}.
Proof.
Admitted. (* TODO *)

Lemma DTL120_4 C Gamma A :
  Gamma |- C, {A: eventually^ eventually A =>> eventually^ A}.
Proof.
Admitted. (* TODO *)

Lemma DTL121 C Gamma A :
  Gamma |- C, {A: eventually^ A -> eventually A}.
Proof.
  by apply DSIfC, DSOrCR.
Qed.

Lemma DTL122 C Gamma A :
  Gamma |- C, {A: always^ eventually A -> always eventually A}.
Proof.
Admitted. (* TODO *)
