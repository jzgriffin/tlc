Require Import mathcomp.ssreflect.eqtype.
Require Import mathcomp.ssreflect.ssrbool.
Require Import mathcomp.ssreflect.ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Constant for periodic_event events *)
Inductive periodic_event :=
| PE.

(* Equality *)
Section eq.

  (* Boolean equality *)
  Definition periodic_event_eq pl pr :=
    match pl, pr with
    | PE, PE => true
    end.

  (* Boolean equality reflection *)
  Lemma periodic_event_eqP : Equality.axiom periodic_event_eq.
  Proof.
    case; case; by constructor.
  Qed.

  (* EqType canonical structures *)
  Canonical Structure periodic_event_eqMixin :=
    Eval hnf in EqMixin periodic_event_eqP.
  Canonical Structure periodic_event_eqType :=
    Eval hnf in EqType periodic_event periodic_event_eqMixin.

End eq.
