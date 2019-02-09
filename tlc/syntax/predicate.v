Require Import mathcomp.ssreflect.eqtype.
Require Import mathcomp.ssreflect.ssrbool.
Require Import mathcomp.ssreflect.ssreflect.
Require Import tlc.syntax.term.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Forms of logical predicates *)
Inductive predicate :=
| PFalse
| PEqual (tl tr : term)
| PIn (t ts : term)
| PCorrect (tn : term).

(* Equality *)
Section eq.

  (* Boolean equality *)
  Fixpoint predicate_eq pl pr :=
    match pl, pr with
    | PFalse, PFalse => true
    | PFalse, _ => false
    | PEqual tll trl, PEqual tlr trr => (tll == tlr) && (trl == trr)
    | PEqual _ _, _ => false
    | PIn tl tsl, PIn tr tsr => (tl == tr) && (tsl == tsr)
    | PIn _ _, _ => false
    | PCorrect tnl, PCorrect tnr => tnl == tnr
    | PCorrect _, _ => false
    end.

  (* Boolean equality reflection *)
  Lemma predicate_eqP : Equality.axiom predicate_eq.
  Proof.
    elim=> [| tll trl | tl tsl | tnl] [| tlr trr | tr tsr | tnr] //=;
      try by constructor.
    - case H: (tll == tlr); move/eqP: H => H //=; subst;
        last by constructor; move=> [].
      case H: (trl == trr); move/eqP: H => H //=; subst;
        last by constructor; move=> [].
      by constructor.
    - case H: (tl == tr); move/eqP: H => H //=; subst;
        last by constructor; move=> [].
      case H: (tsl == tsr); move/eqP: H => H //=; subst;
        last by constructor; move=> [].
      by constructor.
    - case H: (tnl == tnr); move/eqP: H => H //=; subst;
        last by constructor; move=> [].
      by constructor.
  Qed.

  (* EqType canonical structures *)
  Canonical Structure predicate_eqMixin := EqMixin predicate_eqP.
  Canonical Structure predicate_eqType :=
    Eval hnf in EqType predicate predicate_eqMixin.

End eq.
