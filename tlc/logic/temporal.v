From mathcomp.ssreflect
Require Import ssreflect.
From tlc.assert
Require Import all_assert.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Basic axioms and inference rules of temporal logic *)
Section basic.

  Reserved Notation "|- p"
    (at level 80, no associativity).

  Inductive temporal {C} : @prop C -> Prop :=

  (* Future axioms *)
  | TFX0 p :
    |- (henceforth: p -> p)
  | TFX1 p :
    |- ((next: ~p) <=> ~(next: p))
  | TFX2 p q :
    |- ((next: (p -> q)) <=> ((next: p) -> (next: q)))
  | TFX3 p q :
    |- ((henceforth: (p -> q)) <=> ((henceforth: p) -> (henceforth: q)))
  | TFX4 p :
    |- ((henceforth: p) -> (henceforth: (next: p)))
  | TFX5 p :
    |- ((p =>> next: p) -> (p =>> henceforth: p))
  | TFX6 p q :
    |- ((p unless q) <=> (q \/ (p /\ next: (p unless q))))
  | TFX7 p q :
    |- ((henceforth: p) =>> (p unless q))

  (* Past axioms *)
  | TPX1 p :
    |- ((previous: p) =>> (previous~: p))
  | TPX2 p q :
    |- ((previous~: (p -> q)) <=> ((previous~: p) -> (previous~: q)))
  | TPX3 p q :
    |- ((alwaysbeen: (p -> q)) =>> ((alwaysbeen: p) -> (alwaysbeen: q)))
  | TPX4 p :
    |- ((henceforth: p) -> (henceforth: previous~: p))
  | TPX5 p :
    |- ((p =>> previous~: p) -> (p =>> alwaysbeen: p))
  | TPX6 p q :
    |- ((p backto q) <=> (q \/ (p /\ previous~: (p backto q))))
  | TPX7 :
    |- (previous~: False')

  (* Mixed axioms *)
  | TFX8 p :
    |- (p =>> next: previous: p)
  | TPX8 p :
    |- (p =>> previous~: next: p)

  (* Generalization *)
  | TGen p :
    |- p ->
    |- (henceforth: p)

  (* Universal commutation *)
  | TUC t (x : rigid_var t) p :
    |- ((forall: x, next: p) <=> (next: forall: x, p))

  where "|- p" := (temporal p).

End basic.

Notation "|-t C , p" := (@temporal C p)
  (at level 80, no associativity).
