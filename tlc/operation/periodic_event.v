(* TLC in Coq
 *
 * Module: tlc.operation.periodic_event
 * Purpose: Contains the event type for periodic events.
 *)

From HB Require Import structures.
Require Import mathcomp.ssreflect.eqtype.
Require Import mathcomp.ssreflect.ssrbool.
Require Import mathcomp.ssreflect.ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Constant for periodic events
 * Periodic events carry no data.
 *)
Inductive periodic_event := PE.

(* Equality *)
Section eq.

  (* Boolean equality *)
  Definition periodic_event_eq p1 p2 :=
    match p1, p2 with
    | PE, PE => true
    end.

  (* Boolean equality reflection *)
  Lemma periodic_event_eqP : Equality.axiom periodic_event_eq.
  Proof.
    by case; case; constructor.
  Qed.

  (* EqType canonical structures *)
  HB.instance Definition _ := hasDecEq.Build periodic_event periodic_event_eqP.

End eq.
