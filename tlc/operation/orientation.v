Require Import mathcomp.ssreflect.eqtype.
Require Import mathcomp.ssreflect.ssrbool.
Require Import mathcomp.ssreflect.ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Orientation of events *)
Inductive orientation :=
| ORequest
| OIndication
| OPeriodic.

(* Equality *)
Section eq.

  (* Boolean equality *)
  Definition orientation_eq ol or :=
    match ol, or with
    | ORequest, ORequest => true
    | ORequest, _ => false
    | OIndication, OIndication => true
    | OIndication, _ => false
    | OPeriodic, OPeriodic => true
    | OPeriodic, _ => false
    end.

  (* Boolean equality reflection *)
  Lemma orientation_eqP : Equality.axiom orientation_eq.
  Proof.
    case; case; by constructor.
  Qed.

  (* EqType canonical structures *)
  Canonical Structure orientation_eqMixin :=
    Eval hnf in EqMixin orientation_eqP.
  Canonical Structure orientation_eqType :=
    Eval hnf in EqType orientation orientation_eqMixin.

End eq.
