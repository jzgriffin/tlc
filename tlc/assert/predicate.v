Require Import mathcomp.ssreflect.eqtype.
Require Import mathcomp.ssreflect.ssrbool.
Require Import mathcomp.ssreflect.ssreflect.
Require Import tlc.compute.expression.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Predicate type *)
Inductive predicate : Type :=
| PEqual : expression -> expression -> predicate
| PMember : expression -> expression -> predicate.

(* Equality *)
Section eq.

  (* Boolean equality *)
  Fixpoint predicate_eq pl pr :=
    match pl, pr with
    | PEqual ell erl, PEqual elr err => (ell == elr) && (erl == err)
    | PEqual _ _, _ => false
    | PMember el esl, PMember er esr => (el == er) && (esl == esr)
    | PMember _ _, _ => false
    end.

  (* Boolean equality reflection *)
  Lemma predicate_eqP : Equality.axiom predicate_eq.
  Proof.
    elim=> [ell erl | el esl] [elr err | er esr] //=; try by constructor.
    - case H: (ell == elr); move/eqP: H => H //=; subst;
        last by constructor; move=> [] => *; apply H.
      case H: (erl == err); move/eqP: H => H //=; subst;
        last by constructor; move=> [] => *; apply H.
      by constructor.
    - case H: (el == er); move/eqP: H => H //=; subst;
        last by constructor; move=> [] => *; apply H.
      case H: (esl == esr); move/eqP: H => H //=; subst;
        last by constructor; move=> [] => *; apply H.
      by constructor.
  Qed.

  (* EqType canonical structures *)
  Canonical Structure predicate_eqMixin := EqMixin predicate_eqP.
  Canonical Structure predicate_eqType :=
    Eval hnf in EqType predicate predicate_eqMixin.

End eq.
