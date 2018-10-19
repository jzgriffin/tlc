From mathcomp.ssreflect
Require Import ssreflect seq.
From tlc.assert
Require Import all_assert.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Basic axioms and inference rules of temporal logic *)
Section basic.

  Reserved Notation "X |- p"
    (at level 80, no associativity).

  Inductive temporal {C} : seq (@prop C) -> @prop C -> Prop :=

  (* Future axioms *)
  | TFX0 X p :
    X |- (henceforth: p -> p)
  | TFX1 X p :
    X |- ((next: ~p) <=> ~(next: p))
  | TFX2 X p q :
    X |- ((next: (p -> q)) <=> ((next: p) -> (next: q)))
  | TFX3 X p q :
    X |- ((henceforth: (p -> q)) <=> ((henceforth: p) -> (henceforth: q)))
  | TFX4 X p :
    X |- ((henceforth: p) -> (henceforth: (next: p)))
  | TFX5 X p :
    X |- ((p =>> next: p) -> (p =>> henceforth: p))
  | TFX6 X p q :
    X |- ((p unless q) <=> (q \/ (p /\ next: (p unless q))))
  | TFX7 X p q :
    X |- ((henceforth: p) =>> (p unless q))

  (* Past axioms *)
  | TPX1 X p :
    X |- ((previous: p) =>> (previous~: p))
  | TPX2 X p q :
    X |- ((previous~: (p -> q)) <=> ((previous~: p) -> (previous~: q)))
  | TPX3 X p q :
    X |- ((alwaysbeen: (p -> q)) =>> ((alwaysbeen: p) -> (alwaysbeen: q)))
  | TPX4 X p :
    X |- ((henceforth: p) -> (henceforth: previous~: p))
  | TPX5 X p :
    X |- ((p =>> previous~: p) -> (p =>> alwaysbeen: p))
  | TPX6 X p q :
    X |- ((p backto q) <=> (q \/ (p /\ previous~: (p backto q))))
  | TPX7 X :
    X |- (previous~: False')

  (* Mixed axioms *)
  | TFX8 X p :
    X |- (p =>> next: previous: p)
  | TPX8 X p :
    X |- (p =>> previous~: next: p)

  (* Generalization *)
  | TGen X p :
    X |- p ->
    X |- (henceforth: p)

  (* Universal commutation *)
  | TUC X t (x : rigid_var t) p :
    X |- ((forall: x, next: p) <=> (next: forall: x, p))

  where "X |- p" := (temporal X p).

End basic.

Notation "X |-t C , p" := (@temporal C X p)
  (at level 80, no associativity).
