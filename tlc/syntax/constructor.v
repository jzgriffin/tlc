(* TLC in Coq
 *
 * Module: tlc.syntax.constructor
 * Purpose: Contains the syntax of constructors.
 *)

From HB Require Import structures.
Require Import mathcomp.ssreflect.choice.
Require Import mathcomp.ssreflect.eqtype.
Require Import mathcomp.ssreflect.ssrbool.
Require Import mathcomp.ssreflect.ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Constructors for value terms *)
Inductive constructor :=
(* Unit *)
| CUnit
(* Maybe *)
| CNone
| CSome
(* Either *)
| CLeft
| CRight
(* Pair *)
| CPair
(* Boolean *)
| CFalse
| CTrue
(* Natural *)
| CZero
| CSucc
(* List *)
| CNil
| CCons
(* Orientation *)
| CRequest
| CIndication
| CPeriodic
(* PeriodicEvent *)
| CPE
(* FLRequest *)
| CFLSend
(* FLIndication *)
| CFLDeliver
(* SLRequest *)
| CSLSend
(* SLIndication *)
| CSLDeliver
(* PLRequest *)
| CPLSend
(* PLIndication *)
| CPLDeliver.

(* Equality *)
Section eq.

  (* Boolean equality *)
  Definition constructor_eq f1 f2 :=
    match f1, f2 with
    (* Unit *)
    | CUnit, CUnit => true
    (* Maybe *)
    | CNone, CNone => true
    | CSome, CSome => true
    (* Either *)
    | CLeft, CLeft => true
    | CRight, CRight => true
    (* Pair *)
    | CPair, CPair => true
    (* Boolean *)
    | CFalse, CFalse => true
    | CTrue, CTrue => true
    (* Natural *)
    | CZero, CZero => true
    | CSucc, CSucc => true
    (* List *)
    | CNil, CNil => true
    | CCons, CCons => true
    (* Orientation *)
    | CRequest, CRequest => true
    | CIndication, CIndication => true
    | CPeriodic, CPeriodic => true
    (* PeriodicEvent *)
    | CPE, CPE => true
    (* FLRequest *)
    | CFLSend, CFLSend => true
    (* FLIndication *)
    | CFLDeliver, CFLDeliver => true
    (* SLRequest *)
    | CSLSend, CSLSend => true
    (* SLIndication *)
    | CSLDeliver, CSLDeliver => true
    (* PLRequest *)
    | CPLSend, CPLSend => true
    (* PLIndication *)
    | CPLDeliver, CPLDeliver => true
    (* Unequal *)
    | _, _ => false
    end.

  (* Boolean equality reflection *)
  Lemma constructor_eqP : Equality.axiom constructor_eq.
  Proof.
    by case; case; constructor.
  Qed.

  (* EqType canonical structures *)
  HB.instance Definition _ := hasDecEq.Build constructor constructor_eqP.

End eq.
