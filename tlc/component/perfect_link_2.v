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
  dforall n; dforall n'; dforall m; dif.

  (* By InvLSe *)
  dhave {-A
    self (
      on n, CPLDeliver ' n' ' m \in Fois =>>
      exists: (* c *)
      (n', $$0) \in (Fs' ' n).2 /\
      on n, event[0]<- CSLDeliver ' n' ' ($$0, m)
    )
  -}.
  {
    eapply DSCut; first (repeat dclear; by apply DPInvLSe with
      (A := {-A
        on n, CPLDeliver ' n' ' m \in Fois ->
        exists: (* c *)
        (n', $$0) \in (Fs' ' n).2 /\
        on n, event[0]<- CSLDeliver ' n' ' ($$0, m)
      -});
      [by dautoclosed | by repeat constructor]).

    (* request *)
    difp.
    {
      dforall e; dif; dsplitp; dswap; dsimplp.
      dcase {-t ? e -}; dexistsp e_m; dexistsp e_n'; dtgenp;
        dtsubstep_l; dsimplp; dxchg 0 2; dswap;
        dtsubstep_l; dswap; dclear; dswap.
      dcase {-t ? Fs ' ? Fn -}; dexistsp s_r; dexistsp s_c; dtgenp;
        dtsubstep_l; dsimplp; dswap; dclear.
      dtinjectionp; repeat dsplitp.
      do 2 dclear; dtgenp; dtsubste_l; dclear.
      by dif; dsplitp; dclear; dpmembernilp.
    }

    (* indication *)
    difp.
    {
      dforall i; dforall e; dif; dsplitp; dswap; dsimplp.
      dcase {-t (? i, ? e) -}; dexistsp e_m; dexistsp e_c; dexistsp e_n';
        dtinjectionp.
      dsplitp; dtgenp;
        dxchg 1 2; dtsubstep_l;
        dswap; dxchg 1 3; dtsubstep_l;
        dswap; dclear; dautoeq.
      dswap; dtgenp;
        dtsubstep_l;
        dswap; dxchg 1 2; dtsubstep_l;
        dswap; dclear; dautoeq.
      dcase {-t ? Fs ' ? Fn -}; dexistsp s_r; dexistsp s_c; dtgenp;
        dtsubstep_l; dsimplp; dswap; dclear.
      dcase {-t FCount ' (? e_n', ? e_c) ' ? s_r == 0 -}; dorp; dtgenp;
        dtsubstep_l; dsimplp; dswap; dclear;
        dtinjectionp; repeat dsplitp; dswap; dclear; dswap; dtgenp;
        dtsubste_l; dclear;
        dif; dsplitp; last by dswap; dpmembernilp.
      dexists e_c.
      dtgenp; dxchg 1 2; dtsubste_l; dtsubstep_l; dswap; dclear.
      dtgenp; dtsubste_l; dclear.
      dpmembersingletonp; dtinjectionp; dsplitp.
      do 2 (dtgenp; dtsubste_l; dautoeq; dclear).
      dsplit; [| by dsplit; first duse DPEqual].
      dsimpl; dpmembersetunion; dright.
      by duse DPMemberSingleton; dforallp {-t (e_n', e_c) -}.
    }

    (* periodic *)
    difp.
    {
      dif; dsplitp; dswap; dsimplp.
      dtinjectionp; repeat dsplitp;  do 2 dclear; dtgenp; dtsubste_l.
      by dif; dsplitp; dclear; dpmembernilp.
    }

    by [].
  }

  (* By lemma 90 *)
  eapply DSCut; first (by repeat dclear; apply DTL87 with
    (A := {-A on n, event[0]<- CSLDeliver ' n' ' ($$0, m) -}));
    dtsubstposp.

  (* By lemma 43 *)
  dhave {-A
    forall: (* c *)
    self (
      ((n', $$0) \in (Fs ' n).2 /\
        eventuallyp on n, event[0]<- CSLDeliver ' n' ' ($$0, m)) =>>
        Fn = n -> CPLDeliver ' n' ' m \notin Fois
    )
  -}; first by
    dforall c; duse L43; dforallp n; dforallp n'; dforallp m;
    dforallp c; difp; first by dassumption.

  (* By rule InvSSe *)
  dhave {-A
    forall: (* c *)
    self (
      (n', $$0) \in (Fs ' n).2 =>>
      always ((n', $$0) \in (Fs ' n).2)
    )
  -}.
  {
    dforall c.
    eapply DSCut; first (by repeat dclear; apply DPInvSSe with
      (S0 := {-A forall: (* s *) (n', c) \in ($$0).2 -});
      [by [] | by dautoclosed | by repeat constructor]);
      dforallp n.
    (* request *)
    difp.
    {
      dforall s; dforall e; dsimpl; dif.
      dcase {-t ? e -}; dexistsp e_m; dexistsp e_n; dtgenp;
        dtsubste_l; dautoeq; dclear.
      by dcase {-t ? s -}; dexistsp s_r; dexistsp s_c; dtgenp;
        dtsubste_l; dautoeq; dtsubstep_l; dswap; dclear; dsimpl; dsimplp.
    }
    (* indication *)
    difp.
    {
      dforall s; dforall i; dforall e; dsimpl; dif.
      dcase {-t (? i, ? e) -}; dexistsp e_m; dexistsp e_c; dexistsp e_n'; dtgenp;
        dtsubste_l; dautoeq; dclear.
      dcase {-t ? s -}; dexistsp s_r; dexistsp s_c; dtgenp;
        dtsubste_l; dautoeq; dtsubstep_l; dswap; dclear; dsimpl; dsimplp.
      dcase {-t FCount ' (? e_n', ? e_c) ' ? s_r == 0 -}; dorp; dtgenp;
        dtsubste_l; dsimpl; dclear; last by [].
      by dpmembersetunion; dleft.
    }
    (* periodic *)
    difp.
    {
      by dforall s; dsimpl; dif.
    }
    by dsimplp.
  }

  (* By lemma 107 *)
  dhave {-A
    forall: (* c *)
    self (
      eventuallyp (on n, event[0]<- CSLDeliver ' n' ' ($$0, m)) =>>
      always eventuallyp (on n, event[0]<- CSLDeliver ' n' ' ($$0, m))
    )
  -}.
  {
    dforall c.
    eapply DSCut; first (by repeat dclear; apply DTL104 with
      (A := {-A on n, event[0]<- CSLDeliver ' n' ' (c, m) -})).
    by eapply DSCut; first (by eapply DTL129); difp; first by dhead.
  }

  (* From (3) and (4) *)
  dhave {-A
    forall: (* c *)
    self (
      (n', $$0) \in (Fs ' n).2 /\
        eventuallyp (on n, event[0]<- CSLDeliver ' n' ' ($$0, m)) =>>
      always ((n', $$0) \in (Fs ' n).2) /\
        always eventuallyp (on n, event[0]<- CSLDeliver ' n' ' ($$0, m))
    )
  -}.
  {
    dforall c.
    dforallp c; dswap; dforallp c.
    match goal with
    | |- Context _ ({-A self ?A_ -} :: {-A self ?B_ -} :: _) ||- _, _ =>
      eapply DSCut; first (by repeat dclear; apply DTSelfDistribAnd with
        (A := A_) (B := B_))
    end; dsplitp; dclear; difp; first by dsplit; dassumption.
    by dtunionentails; dtsubstposp.
  }
  do 2 (dswap; dclear).

  (* By lemma 100 on (5) and (2) *)
  dhave {-A
    forall: (* c *)
    self (
      (n', $$0) \in (Fs ' n).2 /\
        eventuallyp (on n, event[0]<- CSLDeliver ' n' ' ($$0, m)) =>>
      always (Fn = n -> CPLDeliver ' n' ' m \notin Fois)
    )
  -}.
  {
    dforall c.
    do 2 (dforallp c; dswap).
    match goal with
    | |- context[ {-A always ?A1_ /\ always ?A2_ -} ] =>
      eapply DSCut; first (by repeat dclear; apply DTL128_1 with
        (A := A1_) (B := A2_))
    end; dtsubstp_r.
    match goal with
    | |- Context _ ({-A self ?A_ -} :: {-A self ?B_ -} :: _) ||- _, _ =>
      eapply DSCut; first (by repeat dclear; apply DTSelfDistribAnd with
        (A := A_) (B := B_))
    end; dsplitp; dclear; difp; first by dsplit; dassumption.
    by dtl97; dtsubstposp.
  }
  do 2 (dswap; dclear).

  (* By ASASe on (1) and (6) *)
  eapply DSCut; first (by repeat dclear; apply DPASASe' with
    (S0 := {-A forall: (* s *) (n', $$1) \in ($$0).2 /\
      eventuallyp on n, event[0]<- CSLDeliver ' n' ' ($$1, m) -})
    (A := {-A on n, CPLDeliver ' n' ' m \in Fois -})
    (A' := {-A Fn = n -> CPLDeliver ' n' ' m \notin Fois -});
    [by [] | by dautoclosed | by dautoclosed | by dautoclosed]);
    dforallp n; dsimplp; repeat (difp; first by dassumption).
  do 2 (dswap; dclear).

  (* By lemma 108 on (8) *)
  rewrite /AIf /ANotIn; dsdemorgan_1r; dtgenp.
  dtsubstp_r_keep; dswap; dtsubst_l; dclear; dswap; dclear.
  eapply DSCut; first by dhead.
  dtl105_1; dtsubstposp.
  dswap; eapply DSCut; [eapply DTSelfDistribAnd |]; dsplitp; dclear; difp;
    first by dsplit; [by dhead | by dswap; dhead].
  do 2 (dswap; dclear).
  by dtunionentails; dtsubstposp; dtandelimself; dtsubstp_l.
Qed.

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
