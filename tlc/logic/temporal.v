(* TLC in Coq
 *
 * Module: tlc.logic.temporal
 * Purpose: Contains derived rules and lemmas regarding temporal logic.
 *)

Require Import mathcomp.ssreflect.ssreflect.
Require Import tlc.component.component.
Require Import tlc.logic.derives.
Require Import tlc.syntax.all_syntax.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* These rules and lemmas are taken directly from the appendix *)

Lemma DTL76 C ctx A1 A2 :
  ctx |- C, {A: A1 =>> A2} ->
  ctx |- C, {A: always A1} ->
  ctx |- C, {A: always A2}.
Proof.
Admitted. (* TODO *)

Lemma DTL77 C ctx A1 A2 A3 :
  ctx |- C, {A: A1 =>> A2} ->
  ctx |- C, {A: A2 =>> A3} ->
  ctx |- C, {A: A1 =>> A3}.
Proof.
  (* Used in PLC *)
Admitted. (* TODO *)

Lemma DTL78_1 C ctx A1 A2 :
  ctx |- C, {A: A1 =>> A2} ->
  ctx |- C, {A: next A1 =>> next A2}.
Proof.
Admitted. (* TODO *)

Lemma DTL78_2 C ctx A1 A2 :
  ctx |- C, {A: A1 <=> A2} ->
  ctx |- C, {A: next A1 <=> next A2}.
Proof.
Admitted. (* TODO *)

Lemma DTL79 C ctx A :
  ctx |- C, {A: A =>> next A} ->
  ctx |- C, {A: A =>> always A}.
Proof.
Admitted. (* TODO *)

Lemma DTL80 C ctx A :
  ctx |- C, {A: always A =>> A}.
Proof.
  (* Used in PLC *)
Admitted. (* TODO *)

Lemma DTL81 C ctx A1 A2 :
  ctx |- C, {A: always (A1 /\ A2) <=> always A1 /\ always A2}.
Proof.
Admitted. (* TODO *)

Lemma DTL83_1 C ctx A :
  ctx |- C, {A: eventuallyp A <=> eventuallyp eventuallyp A}.
Proof.
  (* Used in SLC & PLC *)
Admitted. (* TODO *)

Lemma DTL83_2 C ctx A :
  ctx |- C, {A: eventuallyp^ eventuallyp^ A =>> eventuallyp^ A}.
Proof.
Admitted. (* TODO *)

Lemma DTL83_3 C ctx A :
  ctx |- C, {A: eventuallyp eventuallyp^ A =>> eventuallyp^ A}.
Proof.
Admitted. (* TODO *)

Lemma DTL83_4 C ctx A :
  ctx |- C, {A: eventuallyp^ eventuallyp A =>> eventuallyp^ A}.
Proof.
Admitted. (* TODO *)

Lemma DTL84 C ctx A :
  ctx |- C, {A: eventually A <=> eventually eventually A}.
Proof.
  (* Used in PLC *)
Admitted. (* TODO *)

Lemma DTL85 C ctx A1 A2 A3 :
  ctx |- C, {A: A1 =>> eventuallyp A2} ->
  ctx |- C, {A: A2 =>> eventuallyp A3} ->
  ctx |- C, {A: A1 =>> eventuallyp A3}.
Proof.
  (* Used in SLC & PLC *)
Admitted. (* TODO *)

Lemma DTL86 C ctx A1 A2 A3 :
  ctx |- C, {A: A1 =>> eventually A2} ->
  ctx |- C, {A: A2 =>> eventually A3} ->
  ctx |- C, {A: A1 =>> eventually A3}.
Proof.
Admitted. (* TODO *)

Lemma DTL87 C ctx A :
  ctx |- C, {A: A =>> eventuallyp A}.
Proof.
  (* Used in PLC *)
Admitted. (* TODO *)

Lemma DTL90 C ctx A :
  ctx |- C, {A: (self ~A) <=> ~self A}.
Proof.
Admitted. (* TODO *)

Lemma DTL91 C ctx A :
  ctx |- C, {A: A -> previous^ next A}.
Proof.
Admitted. (* TODO *)

Lemma DTL94 C ctx A1 A2 :
  ctx |- C, {A: (A1 =>> A2) /\ A1 -> A2}.
Proof.
Admitted. (* TODO *)

Lemma DTL96_1 C ctx A1 A2 A3 :
  ctx |- C, {A:
    (A1 =>> eventually A2) /\ (A2 =>> A3) ->
    A1 =>> eventually A3
  }.
Proof.
Admitted. (* TODO *)

Lemma DTL96_1_b C ctx A1 A2 A3 :
  ctx |- C, {A:
     (A1 =>> A2) /\ (A2 =>> eventually A3) ->
     A1 =>> eventually A3
  }.
Proof.
Admitted. (* TODO *)

Lemma DTL96_2 C ctx A1 A2 A3 :
  ctx |- C, {A:
    (A1 =>> eventuallyp A2) /\ (A2 =>> A3) ->
    A1 =>> eventuallyp A3
  }.
Proof.
  (* Used in PLC *)
Admitted. (* TODO *)

Lemma DTL96_3 C ctx A1 A2 A3 :
  ctx |- C, {A:
    (A1 =>> eventuallyp^ A2) /\ (A2 =>> A3) ->
    A1 =>> eventuallyp^ A3
  }.
Proof.
Admitted. (* TODO *)

Lemma DTL97 C ctx A1 A2 A3 :
  ctx |- C, {A: (A1 =>> always A2) /\ (A2 =>> A3) -> A1 =>> always A3}.
Proof.
  (* Used in PLC *)
Admitted. (* TODO *)

Lemma DTL98_1 C ctx A :
  ctx |- C, {A: eventuallyp always A =>> A}.
Proof.
  (* Used in PLC *)
Admitted. (* TODO *)

Lemma DTL98_2 C ctx A :
  ctx |- C, {A: eventuallyp always^ A =>> A}.
Proof.
Admitted. (* TODO *)

Lemma DTL98_3 C ctx A :
  ctx |- C, {A: eventuallyp^ always A =>> A}.
Proof.
Admitted. (* TODO *)

Lemma DTL100 C ctx A :
  ctx |- C, {A: A -> alwaysp^ (A =>> self A) =>> A}.
Proof.
Admitted. (* TODO *)

Lemma DTL102_1 C ctx A1 A2 :
  ctx |- C, {A:
    eventually A1 /\ eventually A2 =>>
      eventually (A1 /\ eventually A2) \/
      eventually (A2 /\ eventually A1)
  }.
Proof.
Admitted. (* TODO *)

Lemma DTL102_2 C ctx A1 A2 :
  ctx |- C, {A:
    eventuallyp A1 /\ eventuallyp A2 =>>
      eventuallyp (A1 /\ eventuallyp A2) \/
      eventuallyp (A2 /\ eventuallyp A1)
  }.
Proof.
  (* Used in PLC *)
Admitted. (* TODO *)

Lemma DTL102_3 C ctx A1 A2 :
  ctx |- C, {A:
    eventuallyp A1 /\ eventually A2 =>>
    eventuallyp (A1 /\ eventually A2)
  }.
Proof.
Admitted. (* TODO *)

Lemma DTL103_1 C ctx A :
  ctx |- C, {A: (eventually A /\ always^ ~A) =>> A}.
Proof.
Admitted. (* TODO *)

Lemma DTL103_2 C ctx A :
  ctx |- C, {A: (eventuallyp A /\ alwaysp^ ~A) =>> A}.
Proof.
  (* Used in PLC *)
Admitted. (* TODO *)

Lemma DTL104 C ctx A :
  ctx |- C, {A: eventuallyp A =>> always eventuallyp A}.
Proof.
  (* Used in PLC *)
Admitted. (* TODO *)

Lemma DTL105_1 C ctx A :
  ctx |- C, {A: (A =>> always^ ~A) -> A =>> alwaysp^ ~A}.
Proof.
  (* Used in PLC *)
Admitted. (* TODO *)

Lemma DTL105_1_generalization C ctx A A' x x' :
  ctx |- C, {A:
     (forall: x: A <-> forall: x': A') ->
     ((forall: x: forall: x': A =>> (always^ ~A')) ->
     (forall: x: forall: x': A =>> (alwaysp^ ~A')))
  }.
Proof.
  (* Used in PLC *)
Admitted. (* TODO *)

Lemma DTL105_2 C ctx A :
  ctx |- C, {A: (A =>> alwaysp^ ~A) -> A =>> always^ ~A}.
Proof.
Admitted. (* TODO *)

Lemma DTL106 C ctx A1 A2 :
  ctx |- C, {A: (A1 =>> eventuallyp (A1 =>> A2)) -> A1 =>> A2}.
Proof.
Admitted. (* TODO *)

Lemma DTL107 C ctx A :
  ctx |- C, {A: (alwaysp^ A =>> A) -> always A}.
Proof.
Admitted. (* TODO *)

Lemma DTL108 C ctx A1 A2 :
  ctx |- C, {A:
    (alwaysp^ A1 /\ alwaysp^ A2 =>> A1 /\ A2) -> always (A1 /\ A2)
  }.
Proof.
Admitted. (* TODO *)

Lemma DTL109_1 C ctx A :
  ctx |- C, {A:
    eventuallyp eventually A <=> eventually A \/ eventuallyp A
  }.
Proof.
Admitted. (* TODO *)

Lemma DTL109_2 C ctx A :
  ctx |- C, {A:
    eventuallyp^ eventually A =>> eventually A \/ eventuallyp A
  }.
Proof.
Admitted. (* TODO *)

Lemma DTL109_3 C ctx A :
  ctx |- C, {A:
    eventually eventuallyp A =>> eventually A \/ eventuallyp A
  }.
Proof.
Admitted. (* TODO *)

Lemma DTL109_3_a C ctx A :
  ctx |- C, {A:
    eventually eventuallyp A =>> eventually^ A \/ A \/ eventuallyp^ A
  }.
Proof.
  (* Used in PLC *)
Admitted. (* TODO *)

Lemma DTL109_4 C ctx A :
  ctx |- C, {A:
    eventually eventuallyp^ A =>> eventually A \/ eventuallyp A
  }.
Proof.
Admitted. (* TODO *)

Lemma DTL109_5 C ctx A :
  ctx |- C, {A:
    eventuallyp^ eventually^ A =>> eventually A \/ eventuallyp A
  }.
Proof.
Admitted. (* TODO *)

Lemma DTL111 C ctx A :
  ctx |- C, {A: eventuallyp A <=> self eventuallyp^ A}.
Proof.
Admitted. (* TODO *)

Lemma DTL112 C ctx A1 A2 :
  ctx |- C, {A:
    eventually A1 /\ always A2 =>> eventually (A1 /\ always A2)
  }.
Proof.
Admitted. (* TODO *)

Lemma DTL114 C ctx A :
  ctx |- C, {A: ~eventuallyp^ A <=> alwaysp^ ~A}.
Proof.
  (* Used in PLC *)
Admitted. (* TODO *)

Lemma DTL114_1 C ctx A :
  ctx |- C, {A: ~eventually^ A <=> always^ ~A}.
Proof.
  (* Used in PLC *)
Admitted. (* TODO *)

Lemma DTL115 C ctx A :
  ctx |- C, {A: alwaysp^ A <=> alwaysp previous^ A}.
Proof.
Admitted. (* TODO *)

Lemma DTL116 C ctx A1 A2 :
  ctx |- C, {A:
    A1 /\ eventuallyp^ A2 =>>
    eventuallyp^ (A2 /\ eventually A1)
  }.
Proof.
Admitted. (* TODO *)

Lemma DTL117 C ctx A :
  ctx |- C, {A:
    alwaysp A /\ always A =>>
    alwaysp alwaysp^ A /\ always alwaysp^ A
  }.
Proof.
Admitted. (* TODO *)

Lemma DTL118 C ctx A :
  ctx |- C, {A: eventuallyp^ self A <=> eventuallyp A}.
Proof.
Admitted. (* TODO *)

(* These rules and lemmas are new and do not yet appear in the appendix *)

Lemma DTL119 C ctx A :
  ctx |- C, {A: always^ always A <=> always^ A}.
Proof.
  (* Used in SLC *)
Admitted. (* TODO *)

Lemma DTL120_1 C ctx A :
  ctx |- C, {A: eventually A <=> eventually eventually A}.
Proof.
Admitted. (* TODO *)

Lemma DTL120_2 C ctx A :
  ctx |- C, {A: eventually^ eventually^ A =>> eventually^ A}.
Proof.
Admitted. (* TODO *)

Lemma DTL120_3 C ctx A :
  ctx |- C, {A: eventually eventually^ A =>> eventually^ A}.
Proof.
  (* Used in SLC *)
Admitted. (* TODO *)

Lemma DTL120_4 C ctx A :
  ctx |- C, {A: eventually^ eventually A =>> eventually^ A}.
Proof.
Admitted. (* TODO *)

Lemma DTL121 C ctx A :
  ctx |- C, {A: eventually^ A -> eventually A}.
Proof.
  case: ctx => Delta Gamma.
  by apply DSIfC, DSOrCR.
Qed.

Lemma DTL122 C ctx A :
  ctx |- C, {A: always^ eventually A -> always eventually A}.
Proof.
  (* Used in SLC *)
Admitted. (* TODO *)

Lemma DTL123 C ctx A :
  ctx |- C, {A: eventuallyp^ A -> eventuallyp A}.
Proof.
  case: ctx => Delta Gamma.
  by d_ifc; d_right.
Qed.

Lemma DTL124 C ctx Ap Ac :
  ctx |- C, {A: (Ac /\ always^ (Ap -> Ac)) =>> (Ap =>> Ac)}.
Proof.
  (* Used in PLC *)
Admitted. (* TODO *)

Lemma DTL125 C ctx Ap Ac :
  ctx |- C, {A: (Ap -> (Ap =>> Ac)) =>> (Ap =>> Ac)}.
Proof.
  (* Used in PLC *)
Admitted. (* TODO *)

Lemma DTL126 C ctx A B :
  ctx |- C, {A:
    eventuallyp (eventuallyp A /\ eventually B) ->
    eventuallyp (A /\ eventually B)
  }.
Proof.
  (* Provable by DTL102_3 and DTL83_1 *)
Admitted. (* TODO *)

(* Distribution properties, FD1 and FD2 *)
Lemma DTL127_1 C ctx A B :
  ctx |- C, {A: eventually (A \/ B) <=> (eventually A) \/ (eventually B)}.
Proof.
  (* Used in PLC *)
Admitted. (* TODO *)

Lemma DTL127_2 C ctx A m:
  ctx |- C, {A: eventually (exists: m: A) <=> (exists: m: eventually A)}.
Proof.
  (* Used in PLC *)
Admitted. (* TODO *)

Lemma DTL127_3 C ctx A m:
  ctx |- C, {A: eventuallyp (exists: m: A) <=> (exists: m: eventuallyp A)}.
Proof.
  (* Used in PLC *)
Admitted. (* TODO *)

Lemma DTL127_4 C ctx A B :
  ctx |- C, {A: eventually (A /\ B) =>> (eventually A) /\ (eventually B)}.
Proof.
Admitted. (* TODO *)

Lemma DTL127_5 C ctx A B :
  ctx |- C, {A: eventuallyp (A /\ B) =>> (eventuallyp A) /\ (eventuallyp B)}.
Proof.
  (* Used in PLC *)
Admitted. (* TODO *)

Lemma DTL128_1 C ctx A B :
  ctx |- C, {A: always (A /\ B) <=> (always A) /\ (always B)}.
Proof.
  (* Used in PLC *)
Admitted. (* TODO *)

Lemma DTL128_2 C ctx A :
  ctx |- C, {A: always (forall: "?n": A) <=> (forall: "?n": always A)}.
Proof.
Admitted. (* TODO *)

Lemma DTL128_3 C ctx A B :
  ctx |- C, {A: always^ (A /\ B) <=> (always^ A) /\ (always^ B)}.
Proof.
  (* Used in PLC *)
Admitted. (* TODO *)

Lemma DTL129 C ctx A :
  ctx |- C, {A: A -> self A}.
Proof.
  (* Used in PLC *)
Admitted. (* TODO *)

(* Distribution properties of self *)
Lemma DTL130 C ctx A B :
  ctx |- C, {A: self (A /\ B) <-> self A /\ self B}.
Proof.
  (* Used in PLC *)
Admitted. (* TODO *)

(* Self distributes over if *)
Lemma DTL131 C ctx A B :
  ctx |- C, {A: self (A -> B) -> (self A -> self B)}.
Proof.
  (* Used in PLC *)
Admitted. (* TODO *)

Lemma DTL132 C ctx A1 B1 A2 B2 :
  ctx |- C, {A:
    ((A1 =>> B1) /\ (A2 =>> B2)) ->
    ((A1 /\ A2) =>> (B1 /\ B2))
  }.
Proof.
  (* Used in PLC *)
Admitted. (* TODO *)

Lemma DTL133 C ctx P :
  rigid_predicate P ->
  ctx |-C, {A: eventuallyp P -> P}.
Proof.
  (* Used in PLC *)
Admitted. (* TODO *)
