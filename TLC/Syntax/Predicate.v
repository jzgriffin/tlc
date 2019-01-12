Require Import TLC.Syntax.Expression.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Predicate terms of the language *)
Inductive predicate : Type :=
| PEqual (e1 e2 : expression)
| PMember (e1 e2 : expression)
| PCorrect (e1 : expression).

(* Decidable equality *)
Lemma predicate_eq_dec (p p' : predicate) : {p = p'} + {p <> p'}.
Proof.
  decide equality.
  - destruct (expression_eq_dec e2 e3); [subst; now left | now right].
  - destruct (expression_eq_dec e1 e0); [subst; now left | now right].
  - destruct (expression_eq_dec e2 e3); [subst; now left | now right].
  - destruct (expression_eq_dec e1 e0); [subst; now left | now right].
  - destruct (expression_eq_dec e1 e0); [subst; now left | now right].
Defined.

Definition predicate_eqb p p' :=
  match p, p' with
  | PEqual e1 e2, PEqual e1' e2' =>
    andb (expression_eqb e1 e1') (expression_eqb e2 e2')
  | PMember e1 e2, PMember e1' e2' =>
    andb (expression_eqb e1 e1') (expression_eqb e2 e2')
  | PCorrect e1, PCorrect e1' => expression_eqb e1 e1'
  | _, _ => false
  end.

Lemma predicate_eqb_refl p : predicate_eqb p p = true.
Proof.
  induction p; simpl; now repeat rewrite expression_eqb_refl.
Qed.
