(* TLC in Coq
 *
 * Module: tlc.syntax.literal
 * Purpose: Contains the syntax of literals.
 *)

Require Import mathcomp.ssreflect.eqtype.
Require Import mathcomp.ssreflect.ssrbool.
Require Import mathcomp.ssreflect.ssreflect.
Require Import mathcomp.ssreflect.ssrnat.
Require Import tlc.operation.orientation.
Require Import tlc.operation.periodic_event.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Literal value terms
 * These terms are encoded directly using their Coq equivalents.  This is
 * possible because these terms are not constructed from other embedded terms,
 * but from Coq terms of particular types.  In the case of nat, this is
 * particularly helpful because Coq is able to print nat literals using
 * numeric notation; if the naturals were instead implemented through embedded
 * constructors, their full Peano encodings would be printed.
 *
 * NOTE: When adding a new literal constructor, also add its corresponding
 * pattern(s) to the pattern type.
 *)
Inductive literal :=
| LUnit (u : unit)
| LBoolean (b : bool)
| LNatural (n : nat)
| LOrientation (o : orientation)
| LPeriodic (p : periodic_event).

(* Equality *)
Section eq.

  (* Boolean equality *)
  Definition literal_eq ll lr :=
    match ll, lr with
    | LUnit ul, LUnit ur => ul == ur
    | LUnit _, _ => false
    | LBoolean bl, LBoolean br => bl == br
    | LBoolean _, _ => false
    | LNatural nl, LNatural nr => nl == nr
    | LNatural _, _ => false
    | LOrientation ol, LOrientation or => ol == or
    | LOrientation _, _ => false
    | LPeriodic pl, LPeriodic pr => pl == pr
    | LPeriodic _, _ => false
    end.

  (* Boolean equality reflection *)
  Lemma literal_eqP : Equality.axiom literal_eq.
  Proof.
    case=> [ul | bl | nl | ol | pl]; case=> [ur | br | nr | or | pr] //=;
      try by constructor.
    - case H: (ul == ur); move/eqP: H => H //=; subst;
        last by constructor; move=> [].
      by constructor.
    - case H: (bl == br); move/eqP: H => H //=; subst;
        last by constructor; move=> [].
      by constructor.
    - case H: (nl == nr); move/eqP: H => H //=; subst;
        last by constructor; move=> [].
      by constructor.
    - case H: (ol == or); move/eqP: H => H //=; subst;
        last by constructor; move=> [].
      by constructor.
    - case H: (pl == pr); move/eqP: H => H //=; subst;
        last by constructor; move=> [].
      by constructor.
  Qed.

  (* EqType canonical structures *)
  Canonical Structure literal_eqMixin :=
    Eval hnf in EqMixin literal_eqP.
  Canonical Structure literal_eqType :=
    Eval hnf in EqType literal literal_eqMixin.

End eq.

(* Constructor coercions *)
Coercion LUnit : unit >-> literal.
Coercion LBoolean : bool >-> literal.
Coercion LNatural : nat >-> literal.
Coercion LOrientation : orientation >-> literal.
Coercion LPeriodic : periodic_event >-> literal.
