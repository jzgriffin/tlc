From mathcomp.ssreflect
Require Import ssreflect eqtype ssrbool.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Tactics for minimizing Equality.axiom proofs for inductive types *)
Ltac indeq_auto := rewrite //=; try constructor; try assumption; try by [].
Ltac indeq_true Hx x' :=
  move/eqP: Hx => ?; subst x'; indeq_auto.
Ltac indeq_false Hx x' :=
  constructor; case=> ?;
  subst x'; rewrite eqxx in Hx; try inversion Hx; indeq_auto.
Ltac indeq_case x x' :=
  case Hx: (x == x').
Ltac indeq x x' :=
  indeq_case x x';
  match goal with
  | [H : (?a == ?a') = true |- _] => indeq_true H a'
  | [H : (?a == ?a') = false |- _] => indeq_false H a'
  end.

(* Typical use case:
 * Inductive maybe {A : eqType} : Type :=
 * | Just (x : A)
 * | Nothing.
 *
 * Definition maybe_eq {A} (m m' : @maybe A) :=
 *   match m, m' with
 *   | Just x, Just x' => x == x'
 *   | Just _, _ => false
 *   | Nothing, Nothing => true
 *   | Nothing, _ => false
 *   end.
 *
 * Lemma maybe_eqP {A} : Equality.axiom (@maybe_eq A).
 * Proof.
 *   case=> [x | ]; case=> [x' | ]; indeq_auto.
 *   - (* Just *) by indeq x x'.
 * Qed.
 *)
