From mathcomp.ssreflect
Require Import ssreflect eqtype ssrbool ssrfun seq.
From tlc.assert
Require Import all_assert.

Require Import comp flc.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section slc.

  Variable node : eqType.
  Variable message : eqType.

  (* Requests *)

  Inductive req_sl_ : Type :=
  | Send_sl : node -> message -> req_sl_.

  (* Equality *)

  Definition eq_req_sl_ (r r' : req_sl_) : bool :=
    match r, r' with
    | Send_sl n m, Send_sl n' m' => [&& n == n' & m == m']
    end.

  Lemma eq_req_sl_P : Equality.axiom eq_req_sl_.
  Proof.
    case => [ n m ];
    case => [ n' m' ];
    rewrite /=; try by constructor.
    - (* Send_sl *)
      case Hn: (n == n');
        [move/eqP: Hn => ?; subst n' | constructor];
        last by case=> ?; subst n'; rewrite eqxx in Hn.
      case Hm: (m == m');
        [move/eqP: Hm => ?; subst m' | constructor];
        last by case=> ?; subst m'; rewrite eqxx in Hm.
      by constructor.
  Qed.

  Canonical req_sl__eqMixin :=
    Eval hnf in EqMixin eq_req_sl_P.
  Canonical req_sl__eqType :=
    Eval hnf in EqType req_sl_ req_sl__eqMixin.

  Definition req_sl := [eqType of req_sl_].

  (* Indications *)

  Inductive ind_sl_ : Type :=
  | Deliver_sl : node -> message -> ind_sl_.

  (* Equality *)

  Definition eq_ind_sl_ (i i' : ind_sl_) : bool :=
    match i, i' with
    | Deliver_sl n m, Deliver_sl n' m' => [&& n == n' & m == m']
    end.

  Lemma eq_ind_sl_P : Equality.axiom eq_ind_sl_.
  Proof.
    case => [ n m ];
    case => [ n' m' ];
    rewrite /=; try by constructor.
    - (* Deliver_sl *)
      case Hn: (n == n');
        [move/eqP: Hn => ?; subst n' | constructor];
        last by case=> ?; subst n'; rewrite eqxx in Hn.
      case Hm: (m == m');
        [move/eqP: Hm => ?; subst m' | constructor];
        last by case=> ?; subst m'; rewrite eqxx in Hm.
      by constructor.
  Qed.

  Canonical ind_sl__eqMixin :=
    Eval hnf in EqMixin eq_ind_sl_P.
  Canonical ind_sl__eqType :=
    Eval hnf in EqType ind_sl_ ind_sl__eqMixin.

  Definition ind_sl := [eqType of ind_sl_].

  (* State *)

  Definition slc_state := seq (prod node message).

  (* Component *)

  Definition slc_subcomps :=
    [:: Subcomp (req_fl node message)
                (ind_fl node message)].
  Definition slc :=
    let flc := 0 in
    let slc_init n := [::] in
    let slc_request n s ir :=
      match ir with
      | Send_sl n' m =>
        ((n', m) :: s, [:: Send_fl n' m], [::])
      end in
    let slc_indication n' s ii :=
      match ii with
      | Deliver_fl n m =>
        (s, [::], [:: Deliver_sl n m])
      end in
    let slc_periodic n s :=
      let ors := [seq Send_fl p.1 p.2 | p <- s] in
      (s, ors, [::]) in
    @Comp node req_sl ind_sl slc_subcomps
      slc_state slc_init
      slc_request slc_indication slc_periodic.

  (* Specification *)

  Section spec.

    Import AssertNotations.

    Local Notation Vrn' := (first_var).
    Local Notation Vrm := (next_var Vrn').

    (* Non-compiling
    (* SL_1: Stubborn delivery *)
    Definition SL_1 :=
      ((Pcorrect?(Vrn)) /\ (Pcorrect?(Vrn')) ->
      (on: Vrn, ev: [], Creq_ev, (Send_sl Vrn' Vrm) =>
       alwaysf: eventf: on: Vrn', ev: [], Cind_ev, (Deliver_sl Vrn Vrm)))%A.

    (* SL_2: No-forge *)
    Definition SL_2 :=
      (on: Vrn, ev: [], Cind_ev, (Deliver_sl Vrn' Vrm) <~
      on: Vrn', ev: [], Creq_ev, (Send_sl Vrn Vrm))%A.
    *)

  End spec.

End slc.
