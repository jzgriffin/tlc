(* TLC in Coq
 *
 * Module: tlc.syntax.rigid
 * Purpose: Contains the syntax of rigid variables.
 *)

Require Import Coq.Strings.String.
Require Import mathcomp.ssreflect.eqtype.
Require Import mathcomp.ssreflect.ssrbool.
Require Import mathcomp.ssreflect.ssreflect.
Require Import tlc.utility.string.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Type of rigid variables bound in the model interpretation
 * Rigid variables are represented by human-readable names encoded as ASCII
 * strings.
 *)
Inductive rigid := R (n : string).

(* Equality *)
Section eq.

  (* Boolean equality *)
  Definition rigid_eq x1 x2 :=
    match x1, x2 with
    | R n1, R n2 => n1 == n2
    end.

  (* Boolean equality reflection *)
  Lemma rigid_eqP : Equality.axiom rigid_eq.
  Proof.
    case=> [n1] [n2]; simpl.
    by have [<- | neqx] := n1 =P n2; last (by right; case); constructor.
  Qed.

  (* EqType canonical structures *)
  Definition rigid_eqMixin := EqMixin rigid_eqP.
  Canonical rigid_eqType := EqType rigid rigid_eqMixin.

  Lemma rigid_eqE x y : rigid_eq x y = (x == y).
  Proof.
    by rewrite eqE /=.
  Qed.

End eq.
