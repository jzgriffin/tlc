From mathcomp.ssreflect
Require Import ssreflect eqtype ssrbool.
From tlc.utility
Require Import indeq.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Fair-loss link component *)
Section flc.

  Variable N : eqType. (* Node type *)
  Variable M : eqType. (* Message type *)

  (* Requests *)
  Section req.

    Inductive req_fl_ : Type :=
    | Send_fl : N -> M -> req_fl_.

    (* Equality *)
    Section eq.

      Definition eq_req_fl_ (e e' : req_fl_) :=
        match e, e' with
        | Send_fl n m, Send_fl n' m' => (n == n') && (m == m')
        end.

      Lemma eq_req_fl_P : Equality.axiom eq_req_fl_.
      Proof.
        case=> [n m]; case=> [n' m']; indeq_auto.
        - (* Send_fl *) indeq n n'; indeq m m'; by [].
      Qed.

      Canonical req_fl__eqMixin :=
        Eval hnf in EqMixin eq_req_fl_P.
      Canonical req_fl__eqType :=
        Eval hnf in EqType req_fl_ req_fl__eqMixin.

    End eq.

    Definition req_fl := [eqType of req_fl_].

  End req.

  (* Indications *)
  Section ind.

    Inductive ind_fl_ : Type :=
    | Deliver_fl : N -> M -> ind_fl_.

    (* Equality *)
    Section eq.

      Definition eq_ind_fl_ (e e' : ind_fl_) :=
        match e, e' with
        | Deliver_fl n m, Deliver_fl n' m' => (n == n') && (m == m')
        end.

      Lemma eq_ind_fl_P : Equality.axiom eq_ind_fl_.
      Proof.
        case=> [n m]; case=> [n' m']; indeq_auto.
        - (* Deliver_fl *) indeq n n'; indeq m m'; by [].
      Qed.

      Canonical ind_fl__eqMixin :=
        Eval hnf in EqMixin eq_ind_fl_P.
      Canonical ind_fl__eqType :=
        Eval hnf in EqType ind_fl_ ind_fl__eqMixin.

    End eq.

    Definition ind_fl := [eqType of ind_fl_].

  End ind.

End flc.

Arguments req_fl_ {N M}.
Arguments Send_fl {N M}.
Arguments req_fl {N M}.
Arguments ind_fl_ {N M}.
Arguments Deliver_fl {N M}.
Arguments ind_fl {N M}.
