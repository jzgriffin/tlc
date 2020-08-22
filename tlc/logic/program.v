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

Lemma DPTopRequestSelfElim C Delta :
  Context Delta [::] ||- C, {-A
    forall: (* e *)
    event[]-> $$0 /\ self-event <-> event[]-> $$0
  -}.
Proof.
  dforallc e; dsimplfresh; dsplitc; difc; first by dsplitp.
  dsplitc; first by [].
  dsplitp; dswap; dsplitp.
  by dright; dleft; dsplitc; dassumption.
Qed.

Lemma DPTopRequestSelf C Delta :
  Context Delta [::] ||- C, {-A
    forall: (* e *)
    event[]-> $$0 =>> self-event
  -}.
Proof.
Admitted.

Lemma DPSubIndicationSelfElim C Delta :
  Context Delta [::] ||- C, {-A
    forall: forall: (* i, e *)
    event[$$1]<- $$0 /\ self-event <-> event[$$1]<- $$0
  -}.
Proof.
  dforallc i; dforallc e; dsimplfresh; dsplitc; difc; first by dsplitp.
  dsplitc; first by [].
  dsplitp; dswap; dsplitp.
  by dleft; dexistsc i; dsplitc; dassumption.
Qed.

Lemma DPSubIndicationSelf C Delta :
  Context Delta [::] ||- C, {-A
    forall: forall: (* i, e *)
    event[$$1]<- $$0 =>> self-event
  -}.
Proof.
Admitted.

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
  dforallc n; dforallc e; dforallc e'; dsimplfresh.
  difc; dforallp {-t Fs ' n -}.

  eapply DTTrans; last by duse DPOI; dforallp n; dforallp e'; dassumption.
  repeat (rewrite DTEntailsAndSplitC; split).
  - by exact: DTEntailsAndDropRight.
  - by dtentails_r; dtentails_l;
    duse DPTopRequestSelf; dforallp e.

  eapply DTTrans with (A2 := {-A S ' (Fs ' n) /\
    (Fs' ' n, Fors, Fois) = request C ' n ' (Fs ' n) ' e -});
  last by dtgen.

  rewrite DTEntailsAndSplitC; split; first by repeat dtentails_r.
  rewrite -DTEntailsAndAssocP; dtentails_l.
  duse DPIR; dforallp e.
  rewrite /AOn /TFlexible /TRigid; dtifsubste_pl.
  by dttrans; first dtentails_r.
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
  dforallc n; dforallc i; dforallc e; dforallc e'; dsimplfresh.
  difc; dforallp {-t Fs ' n -}.

  eapply DTTrans; last by duse DPOI; dforallp n; dforallp e'; dassumption.
  repeat (rewrite DTEntailsAndSplitC; split).
  - by exact: DTEntailsAndDropRight.
  - by dtentails_r; dtentails_l;
    duse DPSubIndicationSelf; dforallp i; dforallp e.

  eapply DTTrans with (A2 := {-A S ' (Fs ' n) /\
    (Fs' ' n, Fors, Fois) = indication C ' n ' (Fs ' n) ' (i, e) -});
  last by dtgen.

  rewrite DTEntailsAndSplitC; split; first by repeat dtentails_r.
  rewrite -DTEntailsAndAssocP; dtentails_l.
  duse DPII; dforallp i; dforallp e.
  rewrite /AOn /TFlexible /TRigid; dtifsubste_pl.
  by dttrans; first dtentails_r.
Qed.

(*
  (* By InvL *)
  eapply DSCut.
    repeat dclear; apply DPInvL with (A := {-A on n, S ' (Fs ' Fn) -> e' \in Fois -});
      last by repeat constructor.
    move/andP: Hc_S => [Hlc_S Hgc_S]; apply/andP; split;
      first by rewrite /= !andbT.
    rewrite /assertion_gc_in /=; apply/andP; split; first by repeat auto_mem.
    rewrite ?subset_catl; repeat (apply/andP; split); try by repeat auto_mem.
    by assert (H : [:: e', e, i, n & Delta] = foldr cons Delta [:: e'; e; i; n]);
      first by [];
      last by apply subsetT with (xs2 := Delta); first by [];
      rewrite {}H -(cat_foldr_cons _ Delta); exact: subset_catrr.

    difp. (* request *)
      admit.

    difp. (* indication *)
      dforallc i_l; dforallc e_l; dsimplfresh.
      repeat difc.
      dsplitp.
      dxchg0 3; difp.
        dsplitc; first by dassumption.
        match goal with
        | |- _ ||- _, ?A' =>
          eapply DSCut; [
            apply DTReplE with (x := Fn) (t1 := Fn) (t2 := n) (A := A');
            [| by repeat constructor | |]; try by []
          |]
        end.
        - rewrite /assertion_vars /= ?cats0 mem_cat; apply/orP; left.
          rewrite mem_map; last by rewrite /injective; move=> ?? Hx; injection Hx.
          rewrite mem_cat; apply/orP; left; rewrite mem_cat; apply/orP; right.
          by repeat auto_mem.
        dsplitp; dswap; dclear; difp; first by dassumption.
        rewrite /replace_assertion_var /=; dclean.
        rewrite ?replace_rigid_term_flexible_var;
          try by apply computable_term_rigid.
        dsplitp; dclear; difp; last by [].
        dswap; dsplitp.
        admit.
      by [].
*)

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
      S ' (Fs ' Fn) /\
      (Fs' ' Fn, Fors, Fois) = periodic C ' Fn ' (Fs ' Fn) ->
      A
    ) ->
    (
      $$0 \in UCorrect ->
      (self-event -> S ' (Fs ' $$0)) =>>
      always eventually A
    )
  -}.
Proof.
  (* Used in SLC *)
Admitted.
