(* TLC in Coq
 *
 * Module: tlc.syntax.constructor
 * Purpose: Contains the syntax of constructors.
 *)

Require Import mathcomp.ssreflect.eqtype.
Require Import mathcomp.ssreflect.ssrbool.
Require Import mathcomp.ssreflect.ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Constructors for value terms comprised of other terms
 * Value terms comprised of non-term elements, such as the naturals, are
 * represented as literals.
 *)
Inductive constructor :=
(* Product *)
| CPair
(* Sum *)
| CLeft
| CRight
(* List *)
| CNil
| CCons
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
  Definition constructor_eq cl cr :=
    match cl, cr with
    (* Product *)
    | CPair, CPair => true
    | CPair, _ => false
    (* Sum *)
    | CLeft, CLeft => true
    | CLeft, _ => false
    | CRight, CRight => true
    | CRight, _ => false
    (* List *)
    | CNil, CNil => true
    | CNil, _ => false
    | CCons, CCons => true
    | CCons, _ => false
    (* FLRequest *)
    | CFLSend, CFLSend => true
    | CFLSend, _ => false
    (* FLIndication *)
    | CFLDeliver, CFLDeliver => true
    | CFLDeliver, _ => false
    (* SLRequest *)
    | CSLSend, CSLSend => true
    | CSLSend, _ => false
    (* SLIndication *)
    | CSLDeliver, CSLDeliver => true
    | CSLDeliver, _ => false
    (* PLRequest *)
    | CPLSend, CPLSend => true
    | CPLSend, _ => false
    (* PLIndication *)
    | CPLDeliver, CPLDeliver => true
    | CPLDeliver, _ => false
    end.

  (* Boolean equality reflection *)
  Lemma constructor_eqP : Equality.axiom constructor_eq.
  Proof.
    case; case; by constructor.
  Qed.

  (* EqType canonical structures *)
  Canonical Structure constructor_eqMixin :=
    Eval hnf in EqMixin constructor_eqP.
  Canonical Structure constructor_eqType :=
    Eval hnf in EqType constructor constructor_eqMixin.

End eq.
