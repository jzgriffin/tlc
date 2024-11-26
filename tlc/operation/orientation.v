(* TLC in Coq
 *
 * Module: tlc.operation.orientation
 * Purpose: Contains the orientation type for events.
 *)

From HB Require Import structures.
Require Import mathcomp.ssreflect.eqtype.
Require Import mathcomp.ssreflect.ssrbool.
Require Import mathcomp.ssreflect.ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Orientation of events *)
Inductive orientation :=
| ORequest (* Corresponds to the downward-pointing arrow *)
| OIndication (* Corresponds to the upward-pointing arrow *)
| OPeriodic. (* Corresponds to the downward-pointing wavy arrow *)

(* Equality *)
Section eq.

  (* Boolean equality *)
  Definition orientation_eq o1 o2 :=
    match o1, o2 with
    | ORequest, ORequest => true
    | OIndication, OIndication => true
    | OPeriodic, OPeriodic => true
    | _, _ => false
    end.

  (* Boolean equality reflection *)
  Lemma orientation_eqP : Equality.axiom orientation_eq.
  Proof.
    by case; case; constructor.
  Qed.

  (* EqType canonical structures *)
  HB.instance Definition _ := hasDecEq.Build orientation orientation_eqP.

End eq.
