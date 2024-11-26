(* TLC in Coq
 *
 * Module: tlc.syntax.unknown
 * Purpose: Contains the syntax of unknown values.
 *)

From HB Require Import structures.
Require Import mathcomp.ssreflect.choice.
Require Import mathcomp.ssreflect.eqtype.
Require Import mathcomp.ssreflect.ssrbool.
Require Import mathcomp.ssreflect.ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Unknown values are not known locally *)
Inductive unknown :=
| UNodes (* Set of identifiers of participating nodes *)
| UCorrect. (* Set of identifiers of correct nodes *)

(* Equality *)
Section eq.

  (* Boolean equality *)
  Definition unknown_eq u1 u2 :=
    match u1, u2 with
    | UNodes, UNodes => true
    | UCorrect, UCorrect => true
    | _, _ => false
    end.

  (* Boolean equality reflection *)
  Lemma unknown_eqP : Equality.axiom unknown_eq.
  Proof.
    by case; case; constructor.
  Qed.

  (* EqType canonical structures *)
  HB.instance Definition _ := hasDecEq.Build unknown unknown_eqP.

End eq.
