From mathcomp.ssreflect
Require Import ssreflect eqtype ssrbool.
From tlc.utility
Require Import indeq.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Orientation of events *)
Section orientation.

  Inductive orientation : Type :=
  | Request
  | Indication
  | Periodic.

  (* Equality *)
  Section eq.

    Definition orientation_eq (o o' : orientation) :=
      match o, o' with
      | Request, Request => true
      | Indication, Indication => true
      | Periodic, Periodic => true
      | _, _ => false
      end.

    Lemma orientation_eqP : Equality.axiom orientation_eq.
    Proof.
      case; case; by indeq_auto.
    Qed.

    Canonical orientation_eqMixin :=
      EqMixin orientation_eqP.
    Canonical orientation_eqType :=
      Eval hnf in EqType orientation orientation_eqMixin.

  End eq.

End orientation.
