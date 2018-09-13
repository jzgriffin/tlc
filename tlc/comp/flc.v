From mathcomp.ssreflect
Require Import ssreflect eqtype ssrbool.
From tlc.assert
Require Import node_variable message_variable.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section flc.

  Variable node : eqType.
  Variable message : eqType.

  (* Concrete requests *)
  Inductive req_fl_ : Type :=
  | Send_fl : node -> message -> req_fl_.

  (* Equality *)
  Section req_fl__eq.

    Definition eq_req_fl_ (r r' : req_fl_) :=
      match r, r' with
      | Send_fl n m, Send_fl n' m' => (n == n') && (m == m')
      end.

    Lemma eq_req_fl_P : Equality.axiom eq_req_fl_.
    Proof.
      case=> [n m]; case=> [n' m'];
        rewrite /eq_req_fl_ /=; try by constructor.
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

  End req_fl__eq.

  (* Assertion requests *)
  Inductive req_fl_A_ : Type :=
  | Send_fl_A : node_variable -> message_variable -> req_fl_A_.

  (* Equality *)
  Section req_fl_A__eq.

    Definition eq_req_fl_A_ (r r' : req_fl_A_) :=
      match r, r' with
      | Send_fl_A n m, Send_fl_A n' m' => (n == n') && (m == m')
      end.

    Lemma eq_req_fl_A_P : Equality.axiom eq_req_fl_A_.
    Proof.
      case=> [n m]; case=> [n' m'];
        rewrite /eq_req_fl_A_ /=; try by constructor.
      - (* Send_fl_A *)
        case Hn: (n == n');
          [move/eqP: Hn => ?; subst n' | constructor];
          last by case=> ?; subst n'; rewrite eqxx in Hn.
        case Hm: (m == m');
          [move/eqP: Hm => ?; subst m' | constructor];
          last by case=> ?; subst m'; rewrite eqxx in Hm.
        by constructor.
    Qed.

    Canonical req_fl_A__eqMixin :=
      Eval hnf in EqMixin eq_req_fl_A_P.
    Canonical req_fl_A__eqType :=
      Eval hnf in EqType req_fl_A_ req_fl_A__eqMixin.

    Definition req_fl_A := [eqType of req_fl_A_].

  End req_fl_A__eq.

  (* Concrete indications *)
  Inductive ind_fl_ : Type :=
  | Deliver_fl : node -> message -> ind_fl_.

  (* Equality *)
  Section ind_fl__eq.

    Definition eq_ind_fl_ (r r' : ind_fl_) :=
      match r, r' with
      | Deliver_fl n m, Deliver_fl n' m' => (n == n') && (m == m')
      end.

    Lemma eq_ind_fl_P : Equality.axiom eq_ind_fl_.
    Proof.
      case=> [n m]; case=> [n' m'];
        rewrite /eq_ind_fl_ /=; try by constructor.
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

  End ind_fl__eq.

  (* Assertion indications *)
  Inductive ind_fl_A_ : Type :=
  | Deliver_fl_A : node_variable -> message_variable -> ind_fl_A_.

  (* Equality *)
  Section ind_fl_A__eq.

    Definition eq_ind_fl_A_ (r r' : ind_fl_A_) :=
      match r, r' with
      | Deliver_fl_A n m, Deliver_fl_A n' m' => (n == n') && (m == m')
      end.

    Lemma eq_ind_fl_A_P : Equality.axiom eq_ind_fl_A_.
    Proof.
      case=> [n m]; case=> [n' m'];
        rewrite /eq_ind_fl_A_ /=; try by constructor.
      - (* Deliver_fl_A *)
        case Hn: (n == n');
          [move/eqP: Hn => ?; subst n' | constructor];
          last by case=> ?; subst n'; rewrite eqxx in Hn.
        case Hm: (m == m');
          [move/eqP: Hm => ?; subst m' | constructor];
          last by case=> ?; subst m'; rewrite eqxx in Hm.
        by constructor.
    Qed.

    Canonical ind_fl_A__eqMixin :=
      Eval hnf in EqMixin eq_ind_fl_A_P.
    Canonical ind_fl_A__eqType :=
      Eval hnf in EqType ind_fl_A_ ind_fl_A__eqMixin.

    Definition ind_fl_A := [eqType of ind_fl_A_].

  End ind_fl_A__eq.

End flc.
