Require Import TLC.Term.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Basic axioms and inference rules of temporal logic *)
Section temporal_basic.

  Reserved Notation "|- A"
    (at level 80, no associativity).

  Inductive temporal_logic {C} : list (term C Prop) -> term C Prop -> Prop :=

  (* Future axioms *)
  | TemporalFX0 A :
    |- (always: A -> A)
  | TemporalFX1 A :
    |- (next: ~A <=> ~next: A)
  | TemporalFX2 A A' :
    |- (next: (A -> A') <=> (next: A -> next: A'))
  | TemporalFX3 A A' :
    |- (always: (A -> A') <=> (always: A -> always: A'))
  | TemporalFX4 A :
    |- (always: A -> always: next: A)
  | TemporalFX5 A :
    |- ((A =>> next: A) -> (A =>> always: A))

  (* Past axioms *)
  | TemporalPX3 A A' :
    |- (alwaysp: (A -> A') =>> (alwaysp: A -> alwaysp: A'))

  (* Generalization *)
  | TemporalGen A :
    |- A ->
    |- (always: A)

  (* Universal commutation *)
  | TemporalUC T A :
    |- ((forall: x : T, next: A x) <=> (next: forall: x : T, A x))

  where "|- A" := (forall X, temporal_logic X A).

End temporal_basic.

Arguments temporal_logic : clear implicits.

Notation "X |-t C , A" := (temporal_logic C X A)
  (at level 80, no associativity).

(* Derived rules and lemmas *)

(*Lemma Lemma76 {C} (X : list (term C Prop)) (p q : term C Prop) :
  X |-t C, .
Proof.
Admitted. (* TODO *)*)

(*Lemma Lemma77 {C} (X : list (term C Prop)) (p q r : term C Prop) :
  X |-t C, .
Proof.
Admitted. (* TODO *)*)

(*Lemma Lemma78 {C} (X : list (term C Prop)) (p q : term C Prop) :
  X |-t C, .
Proof.
Admitted. (* TODO *)*)

(*Lemma Lemma79 {C} (X : list (term C Prop)) (p : term C Prop) :
  X |-t C, .
Proof.
Admitted. (* TODO *)*)

Lemma Lemma80 {C} (X : list (term C Prop)) (p : term C Prop) :
  X |-t C, (always: p =>> p).
Proof.
Admitted. (* TODO *)

Lemma Lemma81 {C} (X : list (term C Prop)) (p q : term C Prop) :
  X |-t C, (always: (p /\ q) <=> always: p /\ always: q).
Proof.
Admitted. (* TODO *)

Lemma Lemma83_1 {C} (X : list (term C Prop)) (p : term C Prop) :
  X |-t C, (eventuallyp: p <=> eventuallyp: eventuallyp: p).
Proof.
Admitted. (* TODO *)

Lemma Lemma83_2 {C} (X : list (term C Prop)) (p : term C Prop) :
  X |-t C, (eventuallyp^: eventuallyp^: p =>> eventuallyp^: p).
Proof.
Admitted. (* TODO *)

Lemma Lemma83_3 {C} (X : list (term C Prop)) (p : term C Prop) :
  X |-t C, (eventuallyp: eventuallyp^: p =>> eventuallyp^: p).
Proof.
Admitted. (* TODO *)

Lemma Lemma83_4 {C} (X : list (term C Prop)) (p : term C Prop) :
  X |-t C, (eventuallyp^: eventuallyp: p =>> eventuallyp^: p).
Proof.
Admitted. (* TODO *)

Lemma Lemma84 {C} (X : list (term C Prop)) (p : term C Prop) :
  X |-t C, (eventually: p <=> eventually: eventually: p).
Proof.
Admitted. (* TODO *)

(*Lemma Lemma85 {C} (X : list (term C Prop)) (p q : term C Prop) :
  X |-t C, .
Proof.
Admitted. (* TODO *)*)

(*Lemma Lemma86 {C} (X : list (term C Prop)) (p q r : term C Prop) :
  X |-t C, .
Proof.
Admitted. (* TODO *)*)

Lemma Lemma87 {C} (X : list (term C Prop)) (p : term C Prop) :
  X |-t C, (p =>> eventuallyp: p).
Proof.
Admitted. (* TODO *)

Lemma Lemma90 {C} (X : list (term C Prop)) (p : term C Prop) :
  X |-t C, ((self: ~p) <=> ~self: p).
Proof.
Admitted. (* TODO *)

(*Lemma Lemma91 {C} (X : list (term C Prop)) (p : term C Prop) :
  X |-t C, .
Proof.
Admitted. (* TODO *)*)

Lemma Lemma94 {C} (X : list (term C Prop)) (p q : term C Prop) :
  X |-t C, (((p =>> q) /\ p) -> q).
Proof.
Admitted. (* TODO *)

Lemma Lemma96_1 {C} (X : list (term C Prop)) (p q r : term C Prop) :
  X |-t C, ((p =>> eventually: q) /\ (q =>> r) -> p =>> eventually: r).
Proof.
Admitted. (* TODO *)

Lemma Lemma96_2 {C} (X : list (term C Prop)) (p q r : term C Prop) :
  X |-t C, ((p =>> eventuallyp: q) /\ (q =>> r) -> p =>> eventuallyp: r).
Proof.
Admitted. (* TODO *)

Lemma Lemma96_3 {C} (X : list (term C Prop)) (p q r : term C Prop) :
  X |-t C, ((p =>> eventuallyp^: q) /\ (q =>> r) -> p =>> eventuallyp^: r).
Proof.
Admitted. (* TODO *)

Lemma Lemma97 {C} (X : list (term C Prop)) (p q r : term C Prop) :
  X |-t C, ((p =>> always: q) /\ (q =>> r) -> p =>> always: r).
Proof.
Admitted. (* TODO *)

Lemma Lemma98_1 {C} (X : list (term C Prop)) (p : term C Prop) :
  X |-t C, (eventuallyp: always: p =>> p).
Proof.
Admitted. (* TODO *)

Lemma Lemma98_2 {C} (X : list (term C Prop)) (p : term C Prop) :
  X |-t C, (eventuallyp: always^: p =>> p).
Proof.
Admitted. (* TODO *)

Lemma Lemma98_3 {C} (X : list (term C Prop)) (p : term C Prop) :
  X |-t C, (eventuallyp^: always: p =>> p).
Proof.
Admitted. (* TODO *)

Lemma Lemma100 {C} (X : list (term C Prop)) (p : term C Prop) :
  X |-t C, (p -> (alwaysp^: (p =>> self: p) =>> p)).
Proof.
Admitted. (* TODO *)

Lemma Lemma102_1 {C} (X : list (term C Prop)) (p q : term C Prop) :
  X |-t C, ((eventually: p /\ eventually: q) =>>
    ((p <-> q) \/
      eventually: (p /\ eventually: q) \/
      eventually: (q /\ eventually: p))).
Proof.
Admitted. (* TODO *)

Lemma Lemma102_2 {C} (X : list (term C Prop)) (p q : term C Prop) :
  X |-t C, ((eventuallyp: p /\ eventuallyp: q) =>>
    ((p <-> q) \/
      eventuallyp: (p /\ eventuallyp: q) \/
      eventuallyp: (q /\ eventuallyp: p))).
Proof.
Admitted. (* TODO *)

Lemma Lemma102_3 {C} (X : list (term C Prop)) (p q : term C Prop) :
  X |-t C, ((eventuallyp: p /\ eventually: q) =>>
      eventuallyp: (p /\ eventually: q)).
Proof.
Admitted. (* TODO *)

Lemma Lemma103_1 {C} (X : list (term C Prop)) (p : term C Prop) :
  X |-t C, ((eventually: p /\ always^: ~p) =>> p).
Proof.
Admitted. (* TODO *)

Lemma Lemma103_2 {C} (X : list (term C Prop)) (p : term C Prop) :
  X |-t C, ((eventuallyp: p /\ alwaysp^: ~p) =>> p).
Proof.
Admitted. (* TODO *)

Lemma Lemma104 {C} (X : list (term C Prop)) (p : term C Prop) :
  X |-t C, (eventuallyp: p =>> always: eventuallyp: p).
Proof.
Admitted. (* TODO *)

Lemma Lemma105_1 {C} (X : list (term C Prop)) (p : term C Prop) :
  X |-t C, ((p =>> always^: ~p) -> (p =>> alwaysp^: ~p)).
Proof.
Admitted. (* TODO *)

Lemma Lemma105_2 {C} (X : list (term C Prop)) (p : term C Prop) :
  X |-t C, ((p =>> alwaysp^: ~p) -> (p =>> always^: ~p)).
Proof.
Admitted. (* TODO *)

Lemma Lemma106 {C} (X : list (term C Prop)) (p q : term C Prop) :
  X |-t C, ((p =>> eventuallyp: (p =>> q)) -> (p =>> q)).
Proof.
Admitted. (* TODO *)

Lemma Lemma107 {C} (X : list (term C Prop)) (p : term C Prop) :
  X |-t C, ((alwaysp^: p =>> p) -> always: p).
Proof.
Admitted. (* TODO *)

Lemma Lemma108 {C} (X : list (term C Prop)) (p q : term C Prop) :
  X |-t C, (((alwaysp^: p /\ alwaysp^: q) =>> (p /\ q)) -> always: (p /\ q)).
Proof.
Admitted. (* TODO *)

Lemma Lemma109_1 {C} (X : list (term C Prop)) (p : term C Prop) :
  X |-t C, (eventuallyp: eventually: p <=> eventually: p \/ eventuallyp: p).
Proof.
Admitted. (* TODO *)

Lemma Lemma109_2 {C} (X : list (term C Prop)) (p : term C Prop) :
  X |-t C, (eventuallyp^: eventually: p =>> eventually: p \/ eventuallyp: p).
Proof.
Admitted. (* TODO *)

Lemma Lemma109_3 {C} (X : list (term C Prop)) (p : term C Prop) :
  X |-t C, (eventually: eventuallyp: p =>> eventually: p \/ eventuallyp: p).
Proof.
Admitted. (* TODO *)

Lemma Lemma109_4 {C} (X : list (term C Prop)) (p : term C Prop) :
  X |-t C, (eventually: eventuallyp^: p =>> eventually: p \/ eventuallyp: p).
Proof.
Admitted. (* TODO *)

Lemma Lemma109_5 {C} (X : list (term C Prop)) (p : term C Prop) :
  X |-t C, (eventuallyp^: eventually^: p =>> eventually: p \/ eventuallyp: p).
Proof.
Admitted. (* TODO *)

Lemma Lemma111 {C} (X : list (term C Prop)) (p : term C Prop) :
  X |-t C, ((eventuallyp: p) <=> self: eventuallyp^: p).
Proof.
Admitted. (* TODO *)

Lemma Lemma112 {C} (X : list (term C Prop)) (p q : term C Prop) :
  X |-t C, ((eventually: p /\ always: q) =>> eventually: (p /\ always: q)).
Proof.
Admitted. (* TODO *)

Lemma Lemma114 {C} (X : list (term C Prop)) (p : term C Prop) :
  X |-t C, ((~eventuallyp^: p) =>> alwaysp^: ~p).
Proof.
Admitted. (* TODO *)

(*Lemma Lemma115 {C} (X : list (term C Prop)) (p : term C Prop) :
  X |-t C, .
Proof.
Admitted. (* TODO *)*)

Lemma Lemma116 {C} (X : list (term C Prop)) (p q : term C Prop) :
  X |-t C, ((p /\ eventuallyp^: q) =>> eventuallyp^: (q /\ eventually: p)).
Proof.
Admitted. (* TODO *)

Lemma Lemma117 {C} (X : list (term C Prop)) (p : term C Prop) :
  X |-t C, ((alwaysp: p /\ always: p) =>>
    alwaysp: alwaysp^: p /\ always: alwaysp^: p).
Proof.
Admitted. (* TODO *)

Lemma Lemma118 {C} (X : list (term C Prop)) (p : term C Prop) :
  X |-t C, ((eventuallyp^: self: p) <=> eventuallyp: p).
Proof.
Admitted. (* TODO *)