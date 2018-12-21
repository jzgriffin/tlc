Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Inductive orientation : Type :=
| Request
| Indication
| Periodic.

Definition orientation_eqb (x y : orientation) : bool :=
  match x, y with
  | Request, Request => true
  | Indication, Indication => true
  | Periodic, Periodic => true
  | _, _ => false
  end.

Lemma orientation_eq_dec (x y : orientation) : {x = y} + {x <> y}.
Proof.
  decide equality.
Qed.
