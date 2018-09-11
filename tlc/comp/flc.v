From mathcomp.ssreflect
Require Import ssreflect eqtype ssrbool.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section flc.

  Variable node : eqType.
  Variable message : eqType.

  (* Requests *)

  Inductive req_fl_ : Type :=
  | Send_fl : node -> message -> req_fl_.

  (* Equality *)

  Definition eq_req_fl_ (r r' : req_fl_) : bool :=
    match r, r' with
    | Send_fl n m, Send_fl n' m' => [&& n == n' & m == m']
    end.

  Lemma eq_req_fl_P : Equality.axiom eq_req_fl_.
  Proof.
    case => [ n m ];
    case => [ n' m' ];
    rewrite /=; try by constructor.
    - (* Send_fl *)
      case Hn: (n == n');
        [move/eqP: Hn => ?; subst n' | constructor];
        last by case=> ?; subst n'; rewrite eqxx in Hn.
      case Hm: (m == m');
        [move/eqP: Hm => ?; subst m' | constructor];
        last by case=> ?; subst m'; rewrite eqxx in Hm.
      by constructor.
  Qed.

  Canonical req_fl__eqMixin :=
    Eval hnf in EqMixin eq_req_fl_P.
  Canonical req_fl__eqType :=
    Eval hnf in EqType req_fl_ req_fl__eqMixin.

  Definition req_fl := [eqType of req_fl_].

  (* Indications *)

  Inductive ind_fl_ : Type :=
  | Deliver_fl : node -> message -> ind_fl_.

  (* Equality *)

  Definition eq_ind_fl_ (i i' : ind_fl_) : bool :=
    match i, i' with
    | Deliver_fl n m, Deliver_fl n' m' => [&& n == n' & m == m']
    end.

  Lemma eq_ind_fl_P : Equality.axiom eq_ind_fl_.
  Proof.
    case => [ n m ];
    case => [ n' m' ];
    rewrite /=; try by constructor.
    - (* Deliver_fl *)
      case Hn: (n == n');
        [move/eqP: Hn => ?; subst n' | constructor];
        last by case=> ?; subst n'; rewrite eqxx in Hn.
      case Hm: (m == m');
        [move/eqP: Hm => ?; subst m' | constructor];
        last by case=> ?; subst m'; rewrite eqxx in Hm.
      by constructor.
  Qed.

  Canonical ind_fl__eqMixin :=
    Eval hnf in EqMixin eq_ind_fl_P.
  Canonical ind_fl__eqType :=
    Eval hnf in EqType ind_fl_ ind_fl__eqMixin.

  Definition ind_fl := [eqType of ind_fl_].

End flc.
