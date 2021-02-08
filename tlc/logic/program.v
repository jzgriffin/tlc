(* TLC in Coq
 *
 * Module: tlc.logic.program
 * Purpose: Contains derived rules and lemmas regarding the program logic.
 *)

Require Import mathcomp.ssreflect.eqtype.
Require Import mathcomp.ssreflect.seq.
Require Import mathcomp.ssreflect.ssrbool.
Require Import mathcomp.ssreflect.ssreflect.
Require Import mathcomp.ssreflect.ssrfun.
Require Import mathcomp.ssreflect.ssrnat.
Require Import tlc.component.component.
Require Import tlc.logic.context.
Require Import tlc.logic.derives.
Require Import tlc.logic.predicate.
Require Import tlc.logic.sequent.
Require Import tlc.logic.temporal.
Require Import tlc.operation.periodic_event.
Require Import tlc.semantics.all_semantics.
Require Import tlc.syntax.all_syntax.
Require Import tlc.utility.seq.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* These rules are specific to this implementation *)

Lemma DPLower :
  forall C' Delta A,
  Context Delta [::] ||- C', A ->
  forall C i (TA : top_assertion A),
  Context Delta [::] ||- C, lower_assertion i TA.
Proof.
  (* Used in PLC *)
Admitted.

Lemma DPTopRequestSelfElimIf C Delta A :
  Context Delta [::] ||- C, {-A
    forall: (* e *)
    (self-event -> event[]-> $$0 -> A) <=> (event[]-> $$0 -> A)
  -}.
Proof.
Admitted.
Ltac dptoprequestselfelimif_l :=
  match goal with
  | |- context[ {-A self-event -> event[]-> ?e_ -> ?A_ -} ] =>
    eapply DSCut; first (by repeat dclear; apply DPTopRequestSelfElimIf with
      (A := A_))
  end.

Lemma DPTopRequestSelfElim C Delta :
  Context Delta [::] ||- C, {-A
    forall: (* e *)
    event[]-> $$0 /\ self-event <-> event[]-> $$0
  -}.
Proof.
  dforall e; dsplit; dif; first by dsplitp.
  dsplit; first by [].
  dsplitp; dswap; dsplitp.
  by dright; dleft; dsplit; dassumption.
Qed.

Lemma DPTopRequestSelf C Delta :
  Context Delta [::] ||- C, {-A
    forall: (* e *)
    event[]-> $$0 =>> self-event
  -}.
Proof.
Admitted.
Ltac dptoprequestself :=
  match goal with
  | |- _ ||- _, {-A event[]-> ?e =>> self-event -} =>
    by duse DPTopRequestSelf; dforallp e
  end.

Lemma DPSubIndicationSelfElimIf C Delta A :
  Context Delta [::] ||- C, {-A
    forall: forall: (* i, e *)
    (self-event -> event[$$1]<- $$0 -> A) <=> (event[$$1]<- $$0 -> A)
  -}.
Proof.
Admitted.
Ltac dpsubindicationselfelimif_l :=
  match goal with
  | |- context[ {-A self-event -> event[?i_]<- ?e_ -> ?A_ -} ] =>
    eapply DSCut; first (by repeat dclear; apply DPSubIndicationSelfElimIf with
      (A := A_))
  end.

Lemma DPSubIndicationSelfElim C Delta :
  Context Delta [::] ||- C, {-A
    forall: forall: (* i, e *)
    event[$$1]<- $$0 /\ self-event <-> event[$$1]<- $$0
  -}.
Proof.
  dforall i; dforall e; dsplit; dif; first by dsplitp.
  dsplit; first by [].
  dsplitp; dswap; dsplitp.
  by dleft; dexists i; dsplit; dassumption.
Qed.

Lemma DPSubIndicationSelf C Delta :
  Context Delta [::] ||- C, {-A
    forall: forall: (* i, e *)
    event[$$1]<- $$0 =>> self-event
  -}.
Proof.
Admitted.
Ltac dpsubindicationself :=
  match goal with
  | |- _ ||- _, {-A event[?i]<- ?e =>> self-event -} =>
    by duse DPSubIndicationSelf; dforallp i; dforallp e
  end.

Lemma DPTopPeriodicSelfElimIf C Delta A :
  Context Delta [::] ||- C, {-A
    (self-event -> event[]~> CPE -> A) <=> (event[]~> CPE -> A)
  -}.
Proof.
Admitted.
Ltac dptopperiodicselfelimif_l :=
  match goal with
  | |- context[ {-A self-event -> event[]~> TConstructor CPE -> ?A_ -} ] =>
    eapply DSCut; first (by repeat dclear; apply DPTopPeriodicSelfElimIf with
      (A := A_))
  end.

(* These rules and lemmas are taken directly from the appendix *)

Lemma DPInvL C Delta A :
  assertion_closed_in [::] Delta A ->
  non_temporal_assertion A ->
  Context Delta [::] ||- C, {-A
    (
      forall: (* e *)
      event[]-> $$0 /\
      (Fs' ' Fn, Fors, Fois) = request C ' Fn ' (Fs ' Fn) ' $$0 ->
      A
    ) ->
    (
      forall: forall: (* i, e *)
      event[$$1]<- $$0 /\
      (Fs' ' Fn, Fors, Fois) = indication C ' Fn ' (Fs ' Fn) ' ($$1, $$0) ->
      A
    ) ->
    (
      event[]~> CPE /\
      (Fs' ' Fn, Fors, Fois) = periodic C ' Fn ' (Fs ' Fn) ->
      A
    ) ->
    (
      self-event =>> A
    )
  -}.
Proof.
Admitted.

Lemma DPIROI C Delta S :
  assertion_univ S ->
  assertion_closed_in [::] Delta S ->
  non_temporal_assertion S ->
  Context Delta [::] ||- C, {-A
    forall: forall: forall: (* n, e, e' *)
    (
      forall: (* s *)
      S ' $$0 /\ (Fs' ' $$3, Fors, Fois) = request C ' $$3 ' $$0 ' $$2 ->
      $$1 \in Fois
    ) ->
    (
      on $$2, event[]-> $$1 /\ S ' (Fs ' $$2) =>>
      eventually^ on $$2, event[]<- $$0
    )
  -}.
Proof.
  move=> Hu_S Hc_S NTS.
  dforall n; dforall e; dforall e'.
  dif; dforallp {-t Fs ' n -}.

  eapply DTTrans; last by duse DPOI; dforallp n; dforallp e'; dassumption.
  repeat (rewrite DTEntailsAndSplitC; split).
  - by exact: DTEntailsAndDropRight.
  - by dtentails_r; dtentails_l; dptoprequestself.

  eapply DTTrans with (A2 := {-A S ' (Fs ' n) /\
    (Fs' ' n, Fors, Fois) = request C ' n ' (Fs ' n) ' e -});
  last by dtgen.

  rewrite DTEntailsAndSplitC; split; first by repeat dtentails_r.
  rewrite -DTEntailsAndAssocP; dtentails_l.
  duse DPIR; dforallp e.
  by dtifsubste_pl.
Qed.

Lemma DPIIOI C Delta S :
  assertion_univ S ->
  assertion_closed_in [::] Delta S ->
  non_temporal_assertion S ->
  Context Delta [::] ||- C, {-A
    forall: forall: forall: forall: (* n, i, e, e' *)
    (
      forall: (* s *)
      S ' $$0 /\ (Fs' ' $$4, Fors, Fois) = indication C ' $$4 ' $$0 ' ($$3, $$2) ->
      $$1 \in Fois
    ) ->
    (
      on $$3, event[$$2]<- $$1 /\ S ' (Fs ' $$3) =>>
      eventually^ on $$3, event[]<- $$0
    )
  -}.
Proof.
  move=> Hu_S Hc_S NTS.
  dforall n; dforall i; dforall e; dforall e'.
  dif; dforallp {-t Fs ' n -}.

  eapply DTTrans; last by duse DPOI; dforallp n; dforallp e'; dassumption.
  repeat (rewrite DTEntailsAndSplitC; split).
  - by exact: DTEntailsAndDropRight.
  - by dtentails_r; dtentails_l; dpsubindicationself.

  eapply DTTrans with (A2 := {-A S ' (Fs ' n) /\
    (Fs' ' n, Fors, Fois) = indication C ' n ' (Fs ' n) ' (i, e) -});
  last by dtgen.

  rewrite DTEntailsAndSplitC; split; first by repeat dtentails_r.
  rewrite -DTEntailsAndAssocP; dtentails_l.
  duse DPII; dforallp i; dforallp e.
  by dtifsubste_pl.
Qed.

Lemma DPIISe C Delta :
  Context Delta [::] ||- C, {-A
    forall: forall: (* i, e *)
    self (
      event[$$1]<- $$0 =>>
      (Fs' ' Fn, Fors, Fois) = indication C ' Fn ' (Fs ' Fn) ' ($$1, $$0)
    )
  -}.
Proof.
Admitted.

Lemma DPInvSe C Delta A :
  assertion_closed_in [::] Delta A ->
  Context Delta [::] ||- C, {-A
    self (forall: (* e *) event[]-> $$0 =>> A) ->
    self (forall: forall: (* i, e *) event[$$1]<- $$0 =>> A) ->
    self (event[]~> CPE =>> A) ->
    self always A
  -}.
Proof.
  (* Used in PLC *)
Admitted.

Lemma DPInvLSe C Delta A :
  assertion_closed_in [::] Delta A ->
  non_temporal_assertion A ->
  Context Delta [::] ||- C, {-A
    (
      forall: (* e *)
      event[]-> $$0 /\
      (Fs' ' Fn, Fors, Fois) = request C ' Fn ' (Fs ' Fn) ' $$0 ->
      A
    ) ->
    (
      forall: forall: (* i, e *)
      event[$$1]<- $$0 /\
      (Fs' ' Fn, Fors, Fois) = indication C ' Fn ' (Fs ' Fn) ' ($$1, $$0) ->
      A
    ) ->
    (
      event[]~> CPE /\ (Fs' ' Fn, Fors, Fois) = periodic C ' Fn ' (Fs ' Fn) ->
      A
    ) ->
    (
      self always A
    )
  -}.
Proof.
  (* Used in PLC *)
Admitted.

Lemma DPInvSSe C Delta S :
  assertion_univ S ->
  assertion_closed_in [::] Delta S ->
  non_temporal_assertion S ->
  Context Delta [::] ||- C, {-A
    forall: (* n *)
    (
      forall: forall: (* s, e *)
      S ' $$1 ->
      S ' let: ($0, %, %) := request C ' $$2 ' $$1 ' $$0 in: $$0
    ) ->
    (
      forall: forall: forall: (* s, i, e *)
      S ' $$2 ->
      S ' let: ($0, %, %) := indication C ' $$3 ' $$2 ' ($$1, $$0) in: $$0
    ) ->
    (
      forall: (* s *)
      S ' $$0 ->
      S ' let: ($0, %, %) := periodic C ' $$1 ' $$0 in: $$0
    ) ->
    (
      self (S ' (Fs ' $$0) =>> always (S ' (Fs ' $0)))
    )
  -}.
Proof.
  (* Used in PLC *)
Admitted.

Lemma DPInvS C Delta S :
  assertion_univ S ->
  assertion_closed_in [::] Delta S ->
  non_temporal_assertion S ->
  Context Delta [::] ||- C, {-A
    forall: (* n *)
    (
      forall: forall: (* s, e *)
      S ' $$1 ->
      S ' let: ($0, %, %) := request C ' $$2 ' $$1 ' $$0 in: $$0
    ) ->
    (
      forall: forall: forall: (* s, i, e *)
      S ' $$2 ->
      S ' let: ($0, %, %) := indication C ' $$3 ' $$2 ' ($$1, $$0) in: $$0
    ) ->
    (
      forall: (* s *)
      S ' $$0 ->
      S ' let: ($0, %, %) := periodic C ' $$1 ' $$0 in: $$0
    ) ->
    (
    self-event /\ S ' (Fs ' $$0) =>> (self-event =>> S ' (Fs ' $$0))
    )
  -}.
Proof.
  (* Used in PLC *)
Admitted.

Lemma DPInvS'' C Delta S :
  assertion_univ S ->
  assertion_closed_in [::] Delta S ->
  non_temporal_assertion S ->
  Context Delta [::] ||- C, {-A
    forall: (* n *)
    (
      forall: forall: (* s, e *)
      S ' $$1 ->
      S ' let: ($0, %, %) := request C ' $$2 ' $$1 ' $$0 in: $$0
    ) ->
    (
      forall: forall: forall: (* s, i, e *)
      S ' $$2 ->
      S ' let: ($0, %, %) := indication C ' $$3 ' $$2 ' ($$1, $$0) in: $$0
    ) ->
    (
      forall: (* s *)
      S ' $$0 ->
      S ' let: ($0, %, %) := periodic C ' $$1 ' $$0 in: $$0
    ) ->
    (
      self-event /\ S ' (Fs' ' $$0) =>>
      always^ (self-event -> S ' (Fs ' $$0))
    )
  -}.
Proof.
  (* Used in SLC *)
Admitted.

Lemma DPInvSA C Delta S A :
  assertion_univ S ->
  assertion_closed_in [::] Delta S ->
  assertion_closed_in [::] Delta A ->
  non_temporal_assertion S ->
  non_temporal_assertion A ->
  Context Delta [::] ||- C, {-A
    forall: (* n *)
    ~ S ' (initialize C ' $$0) ->
    (
      forall: (* e *)
      on $$1, event[]-> $$0 /\
      (Fs' ' Fn, Fors, Fois) = request C ' Fn ' (Fs ' Fn) ' $$0 /\
      ~ S ' (Fs ' Fn) /\
      S ' (Fs' ' Fn) ->
      A
    ) ->
    (
      forall: forall: (* i, e *)
      on $$2, event[$$1]<- $$0 /\
      (Fs' ' Fn, Fors, Fois) = indication C ' Fn ' (Fs ' Fn) ' ($$1, $$0) /\
      ~ S ' (Fs ' Fn) /\
      S ' (Fs' ' Fn) ->
      A
    ) ->
    (
      on $$0, event[]~> CPE /\
      (Fs' ' Fn, Fors, Fois) = periodic C ' Fn ' (Fs ' Fn) /\
      ~ S ' (Fs ' Fn) /\
      S ' (Fs' ' Fn) ->
      A
    ) ->
    (
      (self-event /\ S ' (Fs ' $$0)) =>> eventuallyp^ on $$0, A
    )
  -}.
Proof.
  (* Used in SLC & PLC *)
Admitted.

Lemma DPASASe C Delta S A A' :
  assertion_univ S ->
  assertion_closed_in [::] Delta S ->
  assertion_closed_in [::] Delta A ->
  assertion_closed_in [::] Delta A' ->
  Context Delta [::] ||- C, {-A
    forall: (* n *)
    self (A =>> S ' (Fs' ' $$0)) ->
    self (S ' (Fs ' $$0) =>> always A') ->
    self (A =>> always^ A')
  -}.
Proof.
  (* Used in PLC *)
Admitted.

Lemma DPASASe' C Delta S A A' :
  assertion_univ S ->
  assertion_closed_in [:: 1] Delta S ->
  assertion_closed_in [::] Delta A ->
  assertion_closed_in [::] Delta A' ->
  Context Delta [::] ||- C, {-A
    forall: (* n *)
    self (A =>> exists: (S ' (Fs' ' $$1))) ->
    (forall: self (S ' (Fs ' $$1) =>> always A')) ->
    self (A =>> always^ A')
  -}.
Proof.
  (* Used in PLC *)
Admitted.

Lemma DPASA C Delta S A A' :
  assertion_univ S ->
  assertion_closed_in [::] Delta S ->
  assertion_closed_in [::] Delta A ->
  assertion_closed_in [::] Delta A' ->
  non_temporal_assertion S ->
  non_temporal_assertion A ->
  Context Delta [::] ||- C, {-A
    forall: (* n *)
    (self-event /\ A =>> S ' (Fs' ' $$0)) ->
    (self-event /\ S ' (Fs ' $$0) =>> self-event =>> A') ->
    self-event /\ A =>> always^ (self-event -> A')
  -}.
Proof.
  (* Used in PLC *)
Admitted.

Lemma DPAPerSA C Delta S A :
  assertion_univ S ->
  assertion_closed_in [::] Delta S ->
  assertion_closed_in [::] Delta A ->
  non_temporal_assertion S ->
  non_temporal_assertion A ->
  Context Delta [::] ||- C, {-A
    forall: (* n *)
    (
      on $$0, self-event /\
      S ' (Fs ' $$0) /\
      (Fs' ' $$0, Fors, Fois) = periodic C ' $$0 ' (Fs ' $$0) ->
      A
    ) ->
    (
      $$0 \in UCorrect ->
      (self-event =>> S ' (Fs ' $$0)) =>>
      always eventually A
    )
  -}.
Proof.
  (* Used in SLC *)
Admitted.
