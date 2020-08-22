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
| PEqual (x1 x2 : term) (* x1 and x2 are equal *)
| PLess (x1 x2 : term) (* x1 is less than x2 *)
| PMember (y xs : term) (* y is a member of xs *)
| PExtension (xs' xs : term). (* xs' is an extension of xs *)

(* Equality *)
Section eq.

  (* Boolean equality *)
  Definition predicate_eq p1 p2 :=
    match p1, p2 with
    | PEqual x1_1 x1_2, PEqual x2_1 x2_2 => (x1_1 == x2_1) && (x1_2 == x2_2)
    | PLess x1_1 x1_2, PLess x2_1 x2_2 => (x1_1 == x2_1) && (x1_2 == x2_2)
    | PMember y1 xs1, PMember y2 xs2 => (y1 == y2) && (xs1 == xs2)
    | PExtension xs'1 xs1, PExtension xs'2 xs2 => (xs'1 == xs'2) && (xs1 == xs2)
    | _, _ => false
    end.

  (* Boolean equality reflection *)
  Lemma predicate_eqP : Equality.axiom predicate_eq.
  Proof.
    case=>
      [x1_1 x1_2 | x1_1 x1_2 | y1 xs1 | xs'1 xs1]
      [x2_1 x2_2 | x2_1 x2_2 | y2 xs2 | xs'2 xs2]
      //=; try by constructor.
    - have [<- | neqx] := x1_1 =P x2_1; last (by right; case); simpl.
      have [<- | neqx] := x1_2 =P x2_2; last (by right; case); simpl.
      by constructor.
    - have [<- | neqx] := x1_1 =P x2_1; last (by right; case); simpl.
      have [<- | neqx] := x1_2 =P x2_2; last (by right; case); simpl.
      by constructor.
    - have [<- | neqx] := y1 =P y2; last (by right; case); simpl.
      have [<- | neqx] := xs1 =P xs2; last (by right; case); simpl.
      by constructor.
    - have [<- | neqx] := xs'1 =P xs'2; last (by right; case); simpl.
      have [<- | neqx] := xs1 =P xs2; last (by right; case); simpl.
      by constructor.
  Qed.

  (* EqType canonical structures *)
  Definition predicate_eqMixin := EqMixin predicate_eqP.
  Canonical predicate_eqType := EqType predicate predicate_eqMixin.

End eq.
