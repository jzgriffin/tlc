(* TLC in Coq
 *
 * Module: tlc.syntax.variable
 * Purpose: Contains the syntax of variables.
 *)

Require Import mathcomp.ssreflect.choice.
Require Import mathcomp.ssreflect.eqtype.
Require Import mathcomp.ssreflect.ssrbool.
Require Import mathcomp.ssreflect.ssreflect.
Require Import tlc.syntax.flexible.
Require Import tlc.syntax.rigid.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Flexible or rigid variables *)
Inductive variable := VF (x : flexible) | VR (x : rigid).

(* Equality *)
Section eq.

  (* Boolean equality *)
  Definition variable_eq x1 x2 :=
    match x1, x2 with
    | VF x1, VF x2 => x1 == x2
    | VR x1, VR x2 => x1 == x2
    | _, _ => false
    end.

  (* Boolean equality reflection *)
  Lemma variable_eqP : Equality.axiom variable_eq.
  Proof.
    case=> [x1 | x1] [x2 | x2] //=; try by constructor.
    - by have [<- | neqx] := x1 =P x2; last (by right; case); constructor.
    - by have [<- | neqx] := x1 =P x2; last (by right; case); constructor.
  Qed.

  (* EqType canonical structures *)
  Definition variable_eqMixin := EqMixin variable_eqP.
  Canonical variable_eqType := EqType variable variable_eqMixin.

End eq.

(* Constructor coercions *)
Coercion VF : flexible >-> variable.
Coercion VR : rigid >-> variable.
