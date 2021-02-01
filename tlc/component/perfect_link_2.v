(* TLC in Coq
 *
 * Module: tlc.component.perfect_link_2
 * Purpose: Contains the local specification of the perfect link PL_2 property.
 *)

Require Import mathcomp.ssreflect.eqtype.
Require Import mathcomp.ssreflect.seq.
Require Import mathcomp.ssreflect.ssrbool.
Require Import mathcomp.ssreflect.ssreflect.
Require Import mathcomp.ssreflect.ssrnat.
Require Import tlc.component.component.
Require Import tlc.component.perfect_link.
Require Import tlc.logic.all_logic.
Require Import tlc.semantics.all_semantics.
Require Import tlc.syntax.all_syntax.
Require Import tlc.utility.all_utility.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma L44 Delta : Context Delta [::] ||- perfect_link, {-A
  forall: forall: forall: forall: forall: (* n, n', m, c, c' *)
  (on $$3, event[]-> CPLSend ' $$4 ' $$2 =>>
    alwaysp^ ~on $$3, event[]-> CPLSend ' $$4 ' $$2) ->
  self (
    ((on $$4, event[0]<- CSLDeliver ' $$3 ' ($$1, $$2)) /\
      eventuallyp on $$4, event[0]<- CSLDeliver ' $$3 ' ($$0, $$2)) =>>
    $$1 = $$0
  )
-}.
Proof.
Admitted.

Lemma L43 Delta : Context Delta [::] ||- perfect_link, {-A
  forall: forall: forall: forall: (* n, n', m, c *)
  (on $$2, event[]-> CPLSend ' $$3 ' $$1 =>>
    alwaysp^ ~on $$2, event[]-> CPLSend ' $$3 ' $$1) ->
  self (
    (($$2, $$0) \in (Fs ' $$3).2 /\
      eventuallyp on $$3, event[0]<- CSLDeliver ' $$2 ' ($$0, $$1)) =>>
      Fn = $$3 -> CPLDeliver ' $$2 ' $$1 \notin Fois
  )
-}.
Proof.
Admitted.

Lemma L42 Delta : Context Delta [::] ||- perfect_link, {-A
  forall: forall: forall: (* n, n', m *)
  (on $$1, event[]-> CPLSend ' $$2 ' $$0 =>>
    alwaysp^ ~on $$1, event[]-> CPLSend ' $$2 ' $$0) ->
  self (
    (Fn = $$2 /\ CPLDeliver ' $$1 ' $$0 \in Fois) =>>
    always^ (Fn = $$2 -> CPLDeliver ' $$1 ' $$0 \notin Fois) /\
    alwaysp^ (Fn = $$2 -> CPLDeliver ' $$1 ' $$0 \notin Fois)
  )
-}.
Proof.
Admitted.

(* No duplication
 * If a message is sent at most once, it will be delivered at most once.
 *)
Theorem PL_2 Delta : Context Delta [::] ||- perfect_link, {-A
  forall: forall: forall: (* n, n', m *)
  $$2 \in UCorrect /\ $$1 \in UCorrect ->
  (on $$1, event[]-> CPLSend ' $$2 ' $$0 =>> alwaysp^ ~on $$1, event[]-> CPLSend ' $$2 ' $$0) ->
  (on $$2, event[]<- CPLDeliver ' $$1 ' $$0 =>> alwaysp^ ~on $$2, event[]<- CPLDeliver ' $$1 ' $$0)
-}.
Proof.
  dforall n; dforall n'; dforall m; dif; dsplitp; dif.

  (* By OI' *)
  dhave {-A
    on n, event[]<- CPLDeliver ' n' ' m <~
    self-event /\ Fn = n /\ CPLDeliver ' n' ' m \in Fois
  -}.
  {
    duse DPOI'; dforallp n; dforallp {-t CPLDeliver ' n' ' m -}.
    by eapply DSCut; first (by repeat dclear; apply DTL123 with
      (A := {-A self-event /\ Fn = n /\ CPLDeliver ' n' ' m \in Fois -}));
      dtsubstposp.
  }

  (* By InvL *)
  dhave {-A
    self-event /\ Fn = n /\ CPLDeliver ' n' ' m \in Fois =>>
    self-event /\ Fn = n /\ FCount ' (CPLDeliver ' n' ' m) ' Fois = 1
  -}.
  {
    repeat dclear.
    eapply DSCut; first by apply DPInvL with
      (A := {-A
        on n, CPLDeliver ' n' ' m \in Fois ->
        on n, FCount ' (CPLDeliver ' n' ' m) ' Fois = 1
      -});
      [by dautoclosed | by repeat constructor].

    (* request *)
    difp.
    {
      dforall e; dif; dsplitp; dswap; dsimplp.
      dcase {-t ? e -}; dexistsp e_m; dexistsp e_n'; dtgenp;
        dtsubstep_l; dswap; dclear; dsimplp.
      dcase {-t ? Fs ' ? Fn -}; dexistsp s_r; dexistsp s_c; dtgenp;
        dtsubstep_l; dswap; dclear; dsimplp.
      dtinjectionp; repeat dsplitp; do 2 dclear.

      dif; dsplitp; dclear; dswap.
      by dtgenp; dtsubstep_l; dpmembernilp.
    }

    (* indication *)
    difp.
    {
      dforall i; dforall e; dif; dsplitp; dswap; dsimplp.
      dcase {-t (? i, ? e) -}; dexistsp e_m; dexistsp e_c; dexistsp e_n.
      dtinjectionp; dsplitp; do 2 (dtgenp; dswap).
      dxchg 1 2; dtsubstep_l; dsimplp.
      dswap; dxchg 1 3; dtsubstep_l; dautoeq; dswap; dclear.
      dswap; dtsubstep_l.
      dswap; dxchg 1 2; dtsubstep_l; dsimplp; dswap; dclear.
      dcase {-t ? Fs ' ? Fn -}; dexistsp s_r; dexistsp s_c; dtgenp;
        dtsubstep_l; dswap; dclear; dsimplp.
      dcase {-t FCount ' (? e_n, ? e_c) ' ? s_r == 0 -}; dorp; dtgenp;
        dtsubstep_l; dswap; dclear; dsimplp;
        dtinjectionp; repeat dsplitp;
        do 2 dclear; dtgenp;
        dif; dsplitp;
        dsplit; try (by dassumption); dclear; dswap;
        dtsubstep_l; dswap;
        dtsubste_l; dclear.
      - dpmembersingletonp; dtinjectionp; dsplitp;
        dtgenp; dtsubste_l; dautoeq; dclear;
        dtgenp; dtsubste_l; dautoeq; dclear.
        by duse DPCountSingleton; dforallp {-t CPLDeliver ' e_n ' e_m -}.
      - by dpmembernilp.
    }

    (* periodic *)
    difp.
    {
      dif; dsplitp; dswap; dsimplp.
      dtinjectionp; repeat dsplitp; do 2 dclear.
      dif; dsplitp; dclear.
      by dswap; dtgenp; dtsubstep_l; dpmembernilp.
    }

    by dtmergeentailsifp; dtconclhyp_intro_p.
  }

  (* By lemma 99 on (1) and (2) *)
  (* NOTE: Rewriting is easier. *)
  dtsubstposp.

  (* From lemma 42 *)
  duse L42; dforallp n; dforallp n'; dforallp m; difp; first by dassumption.

  (* By SInv in (4) *)
  dhave {-A
    self-event /\ Fn = n /\ CPLDeliver ' n' ' m \in Fois =>>
    always^ (self-event /\ Fn = n -> CPLDeliver ' n' ' m \notin Fois) /\
    alwaysp^ (self-event /\ Fn = n -> CPLDeliver ' n' ' m \notin Fois)
  -}.
  {
    match goal with
    | |- Context _ ({-A self ?A_ -} :: _) ||- _, _ =>
      eapply DSCut; first (by repeat dclear; apply DPSInv_1 with (A := A_));
      difp; first (by []); dswap; dclear
    end.

    dsimplrestrictp.
    by dtmergeentailsifp; dtmergeif; dtsubstp_l.
  }
  dswap; dclear.

  (* From (3) and (5) *)
  dhave {-A
    on n, event[]<- CPLDeliver ' n' ' m <~
    FCount ' (CPLDeliver ' n' ' m) ' Fois = 1 /\
    always^ (self-event /\ Fn = n -> CPLDeliver ' n' ' m \notin Fois) /\
    alwaysp^ (self-event /\ Fn = n -> CPLDeliver ' n' ' m \notin Fois)
  -}.
  {
    dswap.
    dhave {-A
      (self-event /\ on n, FCount ' (CPLDeliver ' n' ' m) ' Fois = 1) ->
      FCount ' (CPLDeliver ' n' ' m) ' Fois = 1 /\
      self-event /\ Fn = n /\ CPLDeliver ' n' ' m \in Fois
    -}.
    {
      repeat dclear.
      dif; dsplitp; dswap; dsplitp.
      repeat (dsplit; first by dassumption).
      dclear; dswap; dclear.

      duse DPMemberCount;
        dforallp {-t CPLDeliver ' n' ' m -};
        dforallp Fois;
        dsplitp; dclear; difp; last by [].
      by duse DPEqualGreaterEqual;
        dforallp {-t FCount ' (CPLDeliver ' n' ' m) ' Fois -};
        dforallp {-t 1 -};
        difp; first by [].
    }

    dtgenp; dclean; dtsubstposp.
    by dswap; dtsubstposp.
  }
  do 2 (dswap; dclear).

  (* By UniOI *)
  dhave {-A
    FCount ' (CPLDeliver ' n' ' m) ' Fois <= 1 /\
    always^ (self-event /\ Fn = n -> CPLDeliver ' n' ' m \notin Fois) /\
    alwaysp^ (self-event /\ Fn = n -> CPLDeliver ' n' ' m \notin Fois) =>>
    on n, event[]<- CPLDeliver ' n' ' m =>>
    alwaysp^ ~on n, event[]<- CPLDeliver ' n' ' m
  -}.
  {
    repeat dclear.
    duse DPUniOI; dforallp n; dforallp Fois; dforallp {-t CPLDeliver ' n' ' m -}.
    by eapply DSCut; first (by repeat dclear; apply DTEntailsAndDropRight with
      (A1 := {-A alwaysp^ ~on n, event[]<- CPLDeliver ' n' ' m -})
      (A2 := {-A always^ ~on n, event[]<- CPLDeliver ' n' ' m -}));
      dtsubstposp.
  }

  (* From (6) and (7) *)
  dswap; duse DPEqualLessEqual;
    dforallp {-t FCount ' (CPLDeliver ' n' ' m) ' Fois -};
    dforallp {-t 1 -};
    dtgenp; dclean; dtsubstposp.
  dswap; dtsubstposp.

  (* Which leads to *)
  eapply DSCut; first (by repeat dclear; apply DTL98_1 with
    (A := {-A
      on n, event[]<- CPLDeliver ' n' ' m ->
      alwaysp^ ~on n, event[]<- CPLDeliver ' n' ' m
    -})); dtsubstposp.

  (* Which leads to *)
  dtmergeentailsifp.
  by dtandelimself; dtsubstp_l.
Qed.
