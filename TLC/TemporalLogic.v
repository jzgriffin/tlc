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
