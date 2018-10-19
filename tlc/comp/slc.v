From mathcomp.ssreflect
Require Import ssreflect eqtype ssrbool ssrfun seq.
From tlc.utility
Require Import indeq hseq.
From tlc.assert
Require Import scope type flexible_var rigid_var term atom prop lib.
From tlc.logic
Require Import all_logic.
From tlc.comp
Require Import component flc.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Stubborn link component *)
Section slc.

  Variable N : eqType. (* Node type *)
  Variable M : eqType. (* Message type *)

  (* Requests *)
  Section req.

    Inductive req_sl_ : Type :=
    | Send_sl : N -> M -> req_sl_.

    (* Equality *)
    Section eq.

      Definition eq_req_sl_ (e e' : req_sl_) :=
        match e, e' with
        | Send_sl n m, Send_sl n' m' => (n == n') && (m == m')
        end.

      Lemma eq_req_sl_P : Equality.axiom eq_req_sl_.
      Proof.
        case=> [n m]; case=> [n' m']; indeq_auto.
        - (* Send_sl *) indeq n n'; indeq m m'; by [].
      Qed.

      Canonical req_sl__eqMixin :=
        Eval hnf in EqMixin eq_req_sl_P.
      Canonical req_sl__eqType :=
        Eval hnf in EqType req_sl_ req_sl__eqMixin.

    End eq.

    Definition req_sl := [eqType of req_sl_].

  End req.

  (* Indications *)
  Section ind.

    Inductive ind_sl_ : Type :=
    | Deliver_sl : N -> M -> ind_sl_.

    (* Equality *)
    Section eq.

      Definition eq_ind_sl_ (e e' : ind_sl_) :=
        match e, e' with
        | Deliver_sl n m, Deliver_sl n' m' => (n == n') && (m == m')
        end.

      Lemma eq_ind_sl_P : Equality.axiom eq_ind_sl_.
      Proof.
        case=> [n m]; case=> [n' m']; indeq_auto.
        - (* Deliver_sl *) indeq n n'; indeq m m'; by [].
      Qed.

      Canonical ind_sl__eqMixin :=
        Eval hnf in EqMixin eq_ind_sl_P.
      Canonical ind_sl__eqType :=
        Eval hnf in EqType ind_sl_ ind_sl__eqMixin.

    End eq.

    Definition ind_sl := [eqType of ind_sl_].

  End ind.

  (* State *)
  Definition state_sl := [eqType of seq (prod N M)].

  (* Component *)
  Definition sub_sl :=
    [:: (@req_fl N M, @ind_fl N M)].
  Definition slc :=
    let flc := 0 in
    let init_sl n := [::] in
    let request_sl n s ir :=
      match ir with
      | Send_sl n' m =>
        ((n', m) :: s, [:: Send_fl n' m], [::])
      end in
    let indication_sl n' s ii :=
      match ii with
      | Deliver_fl n m =>
        (s, [::], [:: Deliver_sl n m])
      end in
    let periodic_sl n s :=
      let ors := [seq Send_fl p.1 p.2 | p <- s] in
      (s, ors, [::]) in
    @Component N M req_sl ind_sl sub_sl
      state_sl init_sl request_sl indication_sl periodic_sl.

End slc.

(* Specification of SLC *)
Module SLCSpec.

Import TLC.

(* Constructors for events *)
Definition Send_sl {N M} :=
  @Const (slc N M) (Node -> Message -> IREvent) (@Send_sl N M).
Definition Deliver_sl {N M} :=
  @Const (slc N M) (Node -> Message -> OIEvent) (@Deliver_sl N M).

Local Notation n := (RigidVar Node 0).
Local Notation n' := (RigidVar Node 1).
Local Notation m := (RigidVar Message 0).

(* SL_1: Stubborn delivery *)
Theorem SL_1 {N M} : [::] |- (slc N M),
  (Atom (correct <- n) /\ Atom (correct <- n') ->
  (on: n, event: [], Request, EventIR <- (Send_sl <- n' <- m)) =>>
  (henceforth: eventually: on: n', event: [], Indication,
    EventOI <- (Deliver_sl <- n <- m))).
Proof.
  (* Assume correct *)
  apply TSequent, SIfR, SAndL, TSequent'.
Admitted. (* TODO *)

(* SL_2: No-forge *)
Theorem SL_2 {N M} : [::] |- (slc N M),
  (on: Fn, event: [], Indication, EventOI <- (Deliver_sl <- n' <- m) <~
  on: n', event: [], Request, EventIR <- (Send_sl <- Fn <- m)).
Proof.
Admitted. (* TODO *)

End SLCSpec.
