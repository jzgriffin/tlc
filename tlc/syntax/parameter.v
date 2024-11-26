(* TLC in Coq
 *
 * Module: tlc.syntax.parameter
 * Purpose: Contains the syntax of parameters.
 *)

From HB Require Import structures.
Require Import mathcomp.ssreflect.choice.
Require Import mathcomp.ssreflect.eqtype.
Require Import mathcomp.ssreflect.ssrbool.
Require Import mathcomp.ssreflect.ssreflect.
Require Import mathcomp.ssreflect.ssrnat.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Type of parameters bound by case at the term level and forall at the
 * assertion level
 * i is the number of binding constructs between the parameter and the construct
 * binding the referenced binder
 * j is the index of the referenced binder within the binding construct
 *)
Inductive parameter := P (i j : nat).

(* Equality *)
Section eq.

  (* Boolean equality *)
  Definition parameter_eq x1 x2 :=
    match x1, x2 with
    | P i1 j1, P i2 j2 => (i1 == i2) && (j1 == j2)
    end.

  (* Boolean equality reflection *)
  Lemma parameter_eqP : Equality.axiom parameter_eq.
  Proof.
    case=> [i1 j1] [i2 j2] //=; try by constructor.
    have [<- | neqx] := i1 =P i2; last (by right; case); simpl.
    have [<- | neqx] := j1 =P j2; last (by right; case); simpl.
    by constructor.
  Qed.

  (* EqType canonical structures *)
  HB.instance Definition _ := hasDecEq.Build parameter parameter_eqP.

End eq.
