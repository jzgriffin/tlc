(* TLC in Coq
 *
 * Module: tlc.syntax.predicate
 * Purpose: Contains the syntax of predicates.
 *)

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
| PEqual (tl tr : term) (* tl and tr are syntactically equal *)
| PGe (tl tr : term) (* tl is greater than or equal to tr *)
| PLe (tl tr : term) (* tl is less than or equal to tr *)
| PIn (t ts : term) (* t is a member of ts *)
| PExtension (ts' ts : term) (* ts' is an extension of ts *)
| PCorrect (tn : term). (* tn is a correct node *)

(* Equality *)
Section eq.

  (* Boolean equality *)
  Fixpoint predicate_eq pl pr :=
    match pl, pr with
    | PFalse, PFalse => true
    | PFalse, _ => false
    | PEqual tll trl, PEqual tlr trr => (tll == tlr) && (trl == trr)
    | PEqual _ _, _ => false
    | PGe tll trl, PGe tlr trr => (tll == tlr) && (trl == trr)
    | PGe _ _, _ => false
    | PLe tll trl, PLe tlr trr => (tll == tlr) && (trl == trr)
    | PLe _ _, _ => false
    | PIn tl tsl, PIn tr tsr => (tl == tr) && (tsl == tsr)
    | PIn _ _, _ => false
    | PExtension ts'l tsl, PExtension ts'r tsr =>
      (ts'l == ts'r) && (tsl == tsr)
    | PExtension _ _, _ => false
    | PCorrect tnl, PCorrect tnr => tnl == tnr
    | PCorrect _, _ => false
    end.

  (* Boolean equality reflection *)
  Lemma predicate_eqP : Equality.axiom predicate_eq.
  Proof.
    elim=> [| tll trl | tll trl | tll trl | tl tsl | ts'l tsl | tnl]
      [| tlr trr | tlr trr | tlr trr | tr tsr | ts'r tsr | tnr] //=;
      try by constructor.
    - case H: (tll == tlr); move/eqP: H => H //=; subst;
        last by constructor; move=> [].
      case H: (trl == trr); move/eqP: H => H //=; subst;
        last by constructor; move=> [].
        by constructor.
    - case H: (tll == tlr); move/eqP: H => H //=; subst;
        last by constructor; move=> [].
      case H: (trl == trr); move/eqP: H => H //=; subst;
        last by constructor; move=> [].
        by constructor.
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
    - case H: (ts'l == ts'r); move/eqP: H => H //=; subst;
        last by constructor; move=> [].
      case H: (tsl == tsr); move/eqP: H => H //=; subst;
        last by constructor; move=> [].
      by constructor.
    - case H: (tnl == tnr); move/eqP: H => H //=; subst;
        last by constructor; move=> [].
      by constructor.
  Qed.

  (* EqType canonical structures *)
  Canonical Structure predicate_eqMixin :=
    Eval hnf in EqMixin predicate_eqP.
  Canonical Structure predicate_eqType :=
    Eval hnf in EqType predicate predicate_eqMixin.

End eq.
