(* TLC in Coq
 *
 * Module: tlc.component.stubborn_link
 * Purpose: Contains the functional implementation and logical specification
 * of the stubborn link component.
 *)

Require Import mathcomp.ssreflect.eqtype.
Require Import mathcomp.ssreflect.seq.
Require Import mathcomp.ssreflect.ssrbool.
Require Import mathcomp.ssreflect.ssreflect.
Require Import mathcomp.ssreflect.ssrnat.
Require Import tlc.component.component.
Require Import tlc.logic.all_logic.
Require Import tlc.operation.orientation.
Require Import tlc.operation.periodic_event.
Require Import tlc.semantics.all_semantics.
Require Import tlc.syntax.all_syntax.
Require Import tlc.utility.monad.
Require Import tlc.utility.result.
Require Import tlc.utility.seq.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Functional implementation *)
Definition stubborn_link :=
  let flc := 0 in
  let initialize :=
    {-t fun: (* n *)
      []
    -} in
  let request :=
    {-t fun: fun: fun: (* n, s, ir *)
      match: $$0 with:
      { CSLSend ' $0 ' $1 (* {n', m} *) ->
        ($$2 :|: [($0, $1)], [(term_of_nat flc, CFLSend ' $0 ' $1)], [])
      }
    -} in
  let indication :=
    {-t fun: fun: fun: (* n, s, ii *)
      match: $$0 with:
      { (pattern_of_nat flc, CFLDeliver ' $0 ' $1) (* {n, m} *) ->
        ($$2, [], [CSLDeliver ' $0 ' $1])
      }
    -} in
  let periodic :=
    {-t fun: fun: (* n, s *)
      ($$0, (fun: (* (n', m) *)
        (term_of_nat flc, CFLSend ' ($$0).1 ' ($$0).2)) <$> $$0, [])
    -} in
  Component
    (Logic.eq_refl : term_computable initialize)
    (Logic.eq_refl : term_computable request)
    (Logic.eq_refl : term_computable indication)
    (Logic.eq_refl : term_computable periodic).

(* Specification *)

(* Stubborn delivery
 * If a correct node n sends a message m to a correct node n', then n'
 * delivers m infinitely often *)
Theorem SL_1 : Z0 ||- stubborn_link, {-A
  forall: forall: forall: (* n, n', m *)
  $$2 \in UCorrect /\ $$1 \in UCorrect ->
  on $$2, event[]-> CSLSend ' $$1 ' $$0 =>>
  always eventually on $$1, event[]<- CSLDeliver ' $$2 ' $$0
-}.
Proof.
  set C := stubborn_link.

  dforall n; dforall n'; dforall m; dsimplfresh.
  dif; dsplitp.

  (* By IR *)
  dhave {-A
    on n, event[]-> CSLSend ' n' ' m =>>
    self-event /\ (n', m) \in (Fs' ' n)
  -}.
  {
    rewrite DTEntailsAndSplitC; split;
      first by dtentails_r; dptoprequestself.

    (* Instantiate IR *)
    duse DPIR; dforallp {-t CSLSend ' n' ' m -}; dsimplp; dtinjectionp.
    dtifsubste_pl; dswap; dclear.
    do 2 (rewrite DTEntailsAndSplitP; dswap; dclear).
    dttrans; dtreple_cl.

    duse DPMemberSetUnion;
    dforallp {-t Fs ' n -}; dforallp {-t [(n', m)] -}; dforallp {-t (n', m) -};
    dtgenp; dclean.
    dtsubst_l; dclear.

    apply DTEntailsOrTautR, DTEntailsAlwaysC.

    duse DPMemberSingleton;
    dforallp {-t (n', m) -};
    dtgenp; dclean.

    by [].
  }

  (* By InvS'' *)
  dhave {-A
    self-event /\ (n', m) \in (Fs' ' n) =>>
    always^ (self-event -> (n', m) \in (Fs ' n))
  -}.
  {
    (* Instantiate InvS'' *)
    set S := {-A forall: (* ts *) (n', m) \in $$0 -}.
    eapply DSCut; [repeat dclear; apply DPInvS'' with (S0 := S);
      [by [] | by dautoclosed | by repeat constructor] |].
    dforallp n; dclean.

    (* request *)
    difp.
      dforall s; dforall e; dif; dsimplp; dsimpl; simpl.
      dcase {-t ? e -}; dexistsp e_n'; dexistsp e_m; dtgenp.
      dtsubste_l; dclean; dsimpl.
      by dpmembersetunion; dleft; dassumption.

    (* indication *)
    difp.
      dforall s; dforall i; dforall e; dif; dsimplp; dsimpl; simpl.
      dcase {-t (? i, ? e) -}; dexistsp e_n'; dexistsp e_m; dtgenp.
      by dtsubste_l; dclean; dsimpl; dassumption.

    (* Prove property for periodics *)
    difp.
      by dforall s; dif; dsimplp; dsimpl; simpl.

    by dsimplp.
  }

  (* From (2) and (3) *)
  dhave {-A
    on n, event[]-> CSLSend ' n' ' m =>>
    always^ (self-event -> (n', m) \in (Fs ' n))
  -}.
  {
    by dswap; dttrans; dassumption.
  }
  do 2 (dswap; dclear).

  (* By APerSA *)
  dhave {-A
    n \in UCorrect -> (self-event =>> (n', m) \in (Fs ' n)) =>>
    always eventually on n,
      (self-event /\ (0, CFLSend ' n' ' m) \in Fors)
  -}.
  {
    dif; dclear.

    (* Instantiate APerSA *)
    set S := {-A forall: (* s *) (n', m) \in $$0 -}.
    set A := {-A on n, (self-event /\ (0, CFLSend ' n' ' m) \in Fors) -}.
    eapply DSCut; [repeat dclear; apply DPAPerSA with (S := S) (A := A);
      [by [] | by dautoclosed | by dautoclosed |
      by repeat constructor | by repeat constructor] |].
    dforallp n; dsimplp; dclean.

    difp.
      repeat dclear.
      dif; repeat (dsplitp; dswap); dtinjectionp; repeat dsplitp.
      repeat (dsplit; first by dassumption).

      dclear; dtgenp; dtsubste_l; dclear.

      set f := {-t fun: (0, CFLSend ' ($$0).1 ' ($$0).2) -}.
      duse DPMemberMap;
        dforallp f; dforallp {-t Fs ' n -}; dforallp {-t (n', m) -};
        dsimplp.
      by dsplitp; dswap; dclear; difp; first by dassumption.

    by difp; first by dassumption.
  }

  (* From (4) and (5) *)
  dhave {-A
    on n, event[]-> CSLSend ' n' ' m =>>
    always^ eventually on n,
      (self-event /\ (0, CFLSend ' n' ' m) \in Fors)
  -}.
  {
    difp; first by dassumption.

    dswap; eapply DSCut; first (by apply DTL119 with (A := {-A
      self-event -> (n', m) \in Fs ' n -})); dclean; dtsubstp_r.
    dswap; dtsubstposp.

    by eapply DSCut; first (by apply DTL119 with (A := {-A
      eventually (on n, self-event /\ (0, CFLSend ' n' ' m) \in Fors) -}));
      dclean; dtsubstp_l.
  }
  do 2 (dswap; dclear).

  (* From OR *)
  (* NOTE: sendfl(n, m) should be sendfl(n', m) *)
  duse DPOR; dforallp n; dforallp {-t 0 -}; dforallp {-t CFLSend ' n' ' m -}.

  (* From (6) and (7) *)
  dtsubstposp.

  (* From lemma 120 on (8) *)
  (* NOTE: Lemma 87 does not apply here; must use new lemma 120 instead *)
  dhave {-A
    on n, event[]-> CSLSend ' n' ' m =>>
      always^ eventually^ on n, event[0]-> CFLSend ' n' ' m
  -}.
  {
    eapply DSCut; first by apply DTL120_3 with (A := {-A
      on n, event[0]-> CFLSend ' n' ' m -}).
    by dtsubstposp.
  }
  dswap; dclear.

  (* By rule FLoss on (1) and (9) *)
  dhave {-A
    on n, event[]-> CSLSend ' n' ' m =>>
    always^ eventually^ on n', event[0]<- CFLDeliver ' n ' m
  -}.
  {
    (* Instantiate FLoss *)
    duse DPFLoss; dforallp n; dforallp n'; dforallp m; dforallp {-t 0 -}.
    difp; first by dassumption.
    by dswap; dttrans; dclear.
  }
  dswap; dclear.

  (* From rule IIOI *)
  dhave {-A
    on n', event[0]<- CFLDeliver ' n ' m =>>
    eventually^ on n', event[]<- CSLDeliver ' n ' m
  -}.
  {
    (* Instantiate IIOI *)
    eapply DSCut; [repeat dclear; eapply DPIIOI with (S0 := {-A forall: ATrue -});
      [by [] | by dautoclosed | by repeat econstructor] |];
      dforallp n'; dforallp {-t 0 -};
      dforallp {-t CFLDeliver ' n ' m -};
      dforallp {-t CSLDeliver ' n ' m -}.

    difp.
      dforall s; dif.
      dsplitp; dclear; dsimplp.
      dtinjectionp; repeat dsplitp.
      dclear; dclear; dtgenp; dtsubste_l.
      by duse DPMemberSingleton; dforallp {-t CSLDeliver ' n ' m -}.

    by dsimplp; eapply DSCut; first (by apply DSAndElimTR with (A := {-A
      event[0]<- CFLDeliver ' n ' m -})); dtgenp; dclean; dtsubst_l; dclear.
  }

  (* From (10) and (11) *)
  dtsubstposp.

  (* From lemma 120 and (12) *)
  dhave {-A
    on n, event[]-> CSLSend ' n' ' m =>>
    always^ eventually^
      on n', event[]<- CSLDeliver ' n ' m
  -}.
  {
    eapply DSCut; first by apply DTL120_2 with (A := {-A
      on n', event[]<- CSLDeliver ' n ' m -}).
    by dtsubstposp.
  }
  dswap; dclear.

  eapply DSCut; first (by apply DTL121 with (A := {-A
    on n', event[]<- CSLDeliver ' n ' m -})); dtsubstposp.
  eapply DSCut; first (by apply DTL122 with (A := {-A
    on n', event[]<- CSLDeliver ' n ' m -})); dtsubstposp.
  by [].
Qed.

(* No-forge
 * If a node n delivers a message m with sender n', then m was previously sent
 * to n by n' *)
Theorem SL_2 : Z0 ||- stubborn_link, {-A
  forall: forall: forall: (* n, n', m *)
  on $$2, event[]<- CSLDeliver ' $$1 ' $$0 <~
  on $$1, event[]-> CSLSend ' $$2 ' $$0
-}.
Proof.
  set C := stubborn_link.

  dforall n; dforall n'; dforall m.

  (* By OI' *)
  dhave {-A
    on n, event[]<- CSLDeliver ' n' ' m =>>
    eventuallyp (self-event /\ on n, (CSLDeliver ' n' ' m \in Fois))
  -}.
  {
    duse DPOI'; dforallp n; dforallp {-t CSLDeliver ' n' ' m -}.
    by eapply DSCut; first (by apply DTL123 with (A := {-A
      self-event /\ on n, CSLDeliver ' n' ' m  \in Fois -})); dtsubstposp.
  }

  (* By InvL *)
  dhave {-A
    (self-event /\ on n, CSLDeliver ' n' ' m \in Fois) =>>
    on n, event[0]<- CFLDeliver ' n' ' m
  -}.
  {
    eapply DSCut; first by repeat dclear; apply DPInvL with (A := {-A
      on n, CSLDeliver ' n' ' m \in Fois ->
      on n, event[0]<- CFLDeliver ' n' ' m -});
      [dautoclosed | repeat constructor].

    (* request *)
    difp.
      dforall e; dif; dsplitp; dswap; dsimplp; dsimpl; simpl; dif; dswap.
      dcase {-t ? e -}; dexistsp e_n'; dexistsp e_m; dtgenp.
      dtsubstep_l; dswap; dclear; dsimplp; dtinjectionp; repeat dsplitp.
      dclear; dclear; dtgenp; dtsubstep_l.
      dsplitp; dclear.
      by duse DPMemberNil; dforallp {-t CSLDeliver ' n' ' m -}; dnotp.

    (* indication *)
    difp.
      dforall i; dforall e; dif; dsplitp; dswap; dsimplp; dsimpl; simpl; dif.
      dsplit; first by dsplitp.
      dswap; dcase {-t (? i, ? e) -}; dexistsp e_m; dexistsp e_n'.
      dtinjectionp; dsplitp.
      dtgenp; dxchg 1 2; dtsubstep_l; dswap; dxchg 1 4; dtsubstep_l; dautoeq;
        dswap; dclear; dswap.
      dtgenp; dtsubstep_l; dswap; dxchg 1 3; dtsubstep_l; dautoeq;
        dswap; dclear; dsimplp.
      dtinjectionp; repeat dsplitp.
      dclear; dclear; dtgenp; dtsubstep_l; dswap; dclear.
      dsplitp; dclear.
      duse DPMemberCons;
        dforallp {-t CSLDeliver ' n' ' m -};
        dforallp {-t CSLDeliver ' e_n' ' e_m -};
        dforallp {-t [] -};
        dsplitp; dswap; dclear; difp; first by [].
      dorp; last by duse DPMemberNil; dforallp {-t CSLDeliver ' n' ' m -}; dnotp.
      dtinjectionp; dsplitp.
      by do 2 (dtgenp; dtsubste_l; dclear; dautoeq); dassumption.

    (* periodic *)
    difp.
      dif; dsplitp; dswap; dsimplp; dsimpl; simpl; dif; dswap.
      dtinjectionp; repeat dsplitp.
      dxchg 0 2; dxchg 1 3; dtgenp; dtsubstep_l.
      dsplitp; dclear.
      by duse DPMemberNil; dforallp {-t CSLDeliver ' n' ' m -}; dnotp.

    by eapply DSCut; first (by apply DSMergeIf with
      (H1 := {-A self-event -})
      (H2 := {-A on n, (CSLDeliver ' n' ' m \in Fois) -})
      (A := {-A on n, event[0]<- CFLDeliver ' n' ' m -}));
      dtgenp; dclean; dtsubst_l; dclear.
  }

  (* From (1) and (2) *)
  dtsubstposp.

  (* By NForge *)
  duse DPNForge; dforallp n'; dforallp n; dforallp m; dforallp {-t 0 -}.

  (* By lemma 85 on (3) and (4) *)
  dhave {-A
    on n, event[]<- CSLDeliver ' n' ' m <~
    on n', event[0]-> CFLSend ' n ' m
  -}.
  {
    by eapply DTL85; first by dexacti 1.
  }
  do 2 (dswap; dclear).

  (* By OR' *)
  dhave {-A
    on n', event[0]-> CFLSend ' n ' m =>>
    eventuallyp (self-event /\ on n', (0, CFLSend ' n ' m) \in Fors)
  -}.
  {
    duse DPOR'; dforallp n'; dforallp {-t 0 -}; dforallp {-t CFLSend ' n ' m -}.
    by eapply DSCut; first (by apply DTL123 with (A := {-A
      self-event /\ on n', ((0, CFLSend ' n ' m) \in Fors) -})); dtsubstposp.
  }

  (* By InvSA *)
  dhave {-A
    (self-event /\ on n', (n, m) \in Fs ' n') =>>
    eventuallyp^ on n', event[]-> CSLSend ' n ' m
  -}.
  {
    eapply DSCut; first by repeat dclear; apply DPInvSA with
      (S0 := {-A forall: (* s *) on n', (n, m) \in $$0 -})
      (A := {-A event[]-> CSLSend ' n ' m -});
      [by [] | by dautoclosed | by dautoclosed |
        by repeat constructor | by repeat constructor].
    dforallp n'.

    (* initialize *)
    difp.
      dsimpl; dnot; dsplitp; dclear.
      by duse DPMemberNil; dforallp {-t (n, m) -}; dnotp.

    (* request *)
    difp.
      dforall e; dsimpl; dif; dsplitp; dswap; dsplitp.
      dcase {-t ? e -}; dexistsp e_m; dexistsp e_n'; dtgenp.
      dtsubstep_l; dswap; dxchg 1 2; dtsubstep_l; dautoeq; dsplitp; dsimplp.
      dtinjectionp; repeat dsplitp.

      dxchg 1 3; dtgenp; dtsubstep_l.
      dsplitp; dswap.
      duse DPMemberSetUnion;
        dforallp {-t Fs ' Fn -}; dforallp {-t [(e_n', e_m)] -}; dforallp {-t (n, m) -}.
      dsplitp; dclear; dtgenp; dclean; dtsubstposp.

      eapply DSCut; first (by apply DSOrDistribAnd2 with
        (A := {-A Fn = n' -})
        (A1 := {-A (n, m) \in Fs ' Fn -})
        (A2 := {-A (n, m) \in [(e_n', e_m)] -}));
        dsplitp; dswap; dclear; difp; first by [].
      dswap; dclear; dclean; dorp; first by dswap; dnotp.
      dsplitp; dclear.

      duse DPMemberCons;
        dforallp {-t (n, m) -};
        dforallp {-t (e_n', e_m) -};
        dforallp {-t [] -};
        dsplitp; dswap; dclear; difp; first by [].
      dorp; last by duse DPMemberNil; dforallp {-t (n, m) -}; dnotp.
      dswap; dclear; dtinjectionp; dsplitp.
      by do 2 (dtgenp; dtsubste_l; dclear; dautoeq); dassumption.

    (* indication *)
    difp.
      dforall i; dforall e; dsimpl; dif; dsplitp; dswap; dsplitp.
      dcase {-t (? i, ? e) -}; dexistsp e_m; dexistsp e_n'; dtgenp.
      dswap; dclear; dtsubstep_l; dautoeq.
      dsplitp; dsimplp; dtinjectionp; repeat dsplitp.
      do 2 (dswap; dclear); dswap; dsplitp.
      dxchg 0 2; dtgenp; dtsubstep_l.
      by dxchg 0 2; dnotp; dassumption.

    (* periodic *)
    difp.
      dsimpl; dif; dsplitp; dswap; dsplitp.
      dclear; dtinjectionp; repeat dsplitp.
      do 2 (dswap; dclear); dswap; dsplitp.
      dxchg 0 2; dtgenp; dtsubstep_l.
      by dxchg 0 2; dnotp; dassumption.

    by dsimplp.
  }

  (* By InvL *)
  dhave {-A
    (self-event /\ on n', (n, m) \in Fs' ' n') =>>
    (self-event /\ on n', (n, m) \in Fs ' n') \/
      on n', event[]-> CSLSend ' n ' m
  -}.
  {
    repeat dclear.
    eapply DSCut; first by apply DPInvL with (A := {-A
      (on n', (n, m) \in Fs' ' n') ->
      (on n', (n, m) \in Fs ' n') \/ on n', event[]-> CSLSend ' n ' m -});
      [by dautoclosed | by repeat constructor].

    (* request *)
    difp.
      dforall e; dif; dsplitp; dswap; dsimplp.
      dcase {-t ? e -}; dexistsp e_m; dexistsp e_n.
      dtgenp; dtsubstep_l; dswap; dxchg 1 2; dtsubstep_l; dswap; dclear.
      dswap; dsimplp; dtinjectionp; repeat dsplitp.

      dif; dsplitp; dtgenp; dtsubste_l; dxchg 1 2; dtsubstep_l; dswap; dclear.
      dtgenp; dtsubstep_l; dswap; dclear.
      duse DPMemberSetUnion;
        dforallp {-t Fs ' n' -}; dforallp {-t [(e_n, e_m)] -}; dforallp {-t (n, m) -}.
      dsplitp; dclear; difp; first by [].
      dorp; [dleft | dright]; dsplit; try (by repeat dclear; apply DPEqual); try by [].

      duse DPMemberCons;
        dforallp {-t (n, m) -};
        dforallp {-t (e_n, e_m) -};
        dforallp {-t [] -};
        dsplitp; dswap; dclear; difp; first by [].
      dorp; last by duse DPMemberNil; dforallp {-t (n, m) -}; dnotp.
      dswap; dclear; dtinjectionp; dsplitp.
      by do 2 (dtgenp; dtsubste_l; dclear; dautoeq); dassumption.

    (* indication *)
    difp.
      dforall i; dforall e; dif; dsplitp; dswap; dsimplp.
      dcase {-t (? i, ? e) -}; dexistsp e_m; dexistsp e_n'.
      dtgenp; dtsubstep_l; dswap; dclear.
      dsimplp; dtinjectionp; repeat dsplitp.

      dif; dsplitp; dleft; dsplit; first by [].
      dtgenp; dxchg 1 2; dtsubstep_l; dswap; dclear.
      by dtgenp; dtsubstep_l.

    (* periodic *)
    difp.
      dif; dsplitp; dswap; dsimplp.
      dtinjectionp; repeat dsplitp.

      dif; dsplitp; dleft; dsplit; first by [].
      dtgenp; dxchg 1 2; dtsubstep_l; dswap; dclear.
      by dtgenp; dtsubstep_l.

    eapply DSCut; first (by repeat dclear; apply DSMergeIf with
      (H1 := {-A self-event -})
      (H2 := {-A on n', (n, m) \in Fs' ' n' -})
      (A := {-A (on n', (n, m) \in Fs ' n') \/
        on n', event[]-> CSLSend ' n ' m -}));
      dtgenp; dclean; dtsubstp_l.
    eapply DSCut; first (by repeat dclear; apply DSIfAndIntro with
      (H1 := {-A self-event -})
      (H2 := {-A on n', (n, m) \in Fs' ' n' -})
      (A := {-A (on n', (n, m) \in Fs ' n') \/
        on n', event[]-> CSLSend ' n ' m -}));
      dtgenp; dclean; dtsubstp_l.
    eapply DSCut; first (by repeat dclear; apply DSOrDistribAnd2 with
      (A := {-A self-event -})
      (A1 := {-A on n', (n, m) \in Fs ' n' -})
      (A2 := {-A on n', event[]-> CSLSend ' n ' m -}));
      dtgenp; dclean; dtsubstp_l.
    eapply DSCut; first (by repeat dclear; apply DSAndComm with
      (A1 := {-A Fn = n' -})
      (A2 := {-A event[]-> CSLSend ' n ' m -}));
      dtgenp; dclean; dtsubstp_l.
    eapply DSCut; first (by repeat dclear; apply DSAndAssoc with
      (A1 := {-A self-event -})
      (A2 := {-A event[]-> CSLSend ' n ' m -})
      (A3 := {-A Fn = n' -}));
      dtgenp; dclean; dtsubstp_r.
    eapply DSCut; first (by repeat dclear; apply DSAndComm with
      (A1 := {-A self-event -})
      (A2 := {-A event[]-> CSLSend ' n ' m -}));
      dtgenp; dclean; dtsubstp_l.
    eapply DSCut; first (by duse DPTopRequestSelfElim;
      dforallp {-t CSLSend ' n ' m -}; dhead);
      dtgenp; dclean; dtsubstp_l.
    by eapply DSCut; first (by repeat dclear; apply DSAndComm with
      (A1 := {-A event[]-> CSLSend ' n ' m -})
      (A2 := {-A Fn = n' -}));
      dtgenp; dclean; dtsubstp_l.
  }

  (* By InvL *)
  dhave {-A
    self-event /\ (on n', (0, CFLSend ' n ' m) \in Fors) =>>
    self-event /\ (on n', (n, m) \in Fs' ' n')
  -}.
  {
    repeat dclear.
    eapply DSCut; first by repeat dclear; apply DPInvL with (A := {-A
      on n', (0, CFLSend ' n ' m) \in Fors ->
      on n', (n, m) \in Fs' ' n'
    -}); [by dautoclosed | by repeat constructor].

    (* request *)
    difp.
      dforall e; dif; dsplitp; dswap; dsimplp.
      dcase {-t ? e -}; dexistsp e_m; dexistsp e_n.
      dtgenp; dtsubstep_l; dswap; dclear; dswap; dclear.
      dsimplp; dtinjectionp; repeat dsplitp.

      dif; dsplitp; dtgenp; dtsubste_l; dxchg 1 2; dtsubstep_l; dswap; dclear.
      dsplit; first by repeat dclear; apply DPEqual.
      dtgenp; dtsubste_l; dclear.
      dswap; dtgenp; dtsubstep_l; dswap; dclear.

      duse DPMemberSetUnion;
        dforallp {-t Fs ' n' -}; dforallp {-t [(e_n, e_m)] -}; dforallp {-t (n, m) -}.
      dsplitp; dswap; dclear; difp; last by [].

      dright.
      duse DPMemberCons;
        dforallp {-t (0, CFLSend ' n ' m) -};
        dforallp {-t (0, CFLSend ' e_n ' e_m) -};
        dforallp {-t [] -};
        dsplitp; dswap; dclear; difp; first by [].
      dorp; last by duse DPMemberNil; dforallp {-t (0, CFLSend ' n ' m) -}; dnotp.
      dswap; dclear; dtinjectionp; dsplitp; dclear; dsplitp.
      do 2 (dtgenp; dtsubste_l; dclear; dautoeq).

      by duse DPMemberSingleton; dforallp {-t (e_n, e_m) -}.

    (* indication *)
    difp.
      dforall i; dforall e; dif; dsplitp; dswap; dsimplp.
      dcase {-t (? i, ? e) -}; dexistsp e_m; dexistsp e_n'.
      dtgenp; dtsubstep_l; dswap; dclear; dswap; dclear.
      dsimplp; dtinjectionp; repeat dsplitp.

      dif; dsplitp; dxchg 0 3; dtgenp; dtsubstep_l; dswap; dclear.
      by duse DPMemberNil; dforallp {-t (0, CFLSend ' n ' m) -}; dnotp.

    (* periodic *)
    difp.
      dif; dsplitp; dswap; dsimplp.
      dtinjectionp; repeat dsplitp.

      dif; dsplitp; dtgenp; dtsubste_l;
        dxchg 1 2; dtsubstep_l; dswap;
        dxchg 1 3; dtsubstep_l; dswap; dclear.
      dsplit; first by repeat dclear; apply DPEqual.

      dtgenp; dtsubstep_l; dswap; dclear.
      dswap; dtgenp; dtsubste_l; dclear.

      set f := {-t fun: (0, CFLSend ' ($$0).1 ' ($$0).2) -};
        duse DPMemberMap;
        dforallp f; dforallp {-t Fs ' n' -}; dforallp {-t (n, m) -}.
      dsplitp; dclear; difp; last by [].
      by dsimpl.

    eapply DSCut; first (by repeat dclear; apply DSMergeIf with
      (H1 := {-A self-event -})
      (H2 := {-A on n', (0, CFLSend ' n ' m) \in Fors -})
      (A := {-A on n', (n, m) \in Fs' ' n' -}));
      dtgenp; dclean; dtsubstp_l.
    by eapply DSCut; first (by repeat dclear; apply DSIfAndIntro with
      (H1 := {-A self-event -})
      (H2 := {-A on n', (0, CFLSend ' n ' m) \in Fors -})
      (A := {-A on n', (n, m) \in Fs' ' n' -}));
      dtgenp; dclean; dtsubstp_l.
  }

  (* By (8) and (9) *)
  dswap; dtsubstposp.

  (* By (6) and (10) *)
  dxchg 1 2; dtsubstposp.

  (* By lemma 83 on (7) and (11) *)
  dhave {-A
    on n', event[0]-> CFLSend ' n ' m <~
    on n', event[]-> CSLSend ' n ' m
  -}.
  {
    dswap; dtsubstposp.
    eapply DSCut; first (by repeat dclear; apply DTOrComm with
      (H1 := {-A eventuallyp^ on n', event[]-> CSLSend ' n ' m -})
      (H2 := {-A on n', event[]-> CSLSend ' n ' m -}));
      dtsubstp_l.
    by eapply DSCut; first (by repeat dclear; apply DTL83_1 with
      (A := {-A on n', event[]-> CSLSend ' n ' m -}));
      dtsubstp_r.
  }
  do 2 (dswap; dclear).

  (* From (5) and (12) *)
  rewrite /APrecededBy; dtsubstposp.

  (* By lemma 83 on (9) *)
  by eapply DSCut; first (by repeat dclear; apply DTL83_1 with
    (A := {-A on n', event[]-> CSLSend ' n ' m -}));
    dtsubstp_r.
Qed.

(* Top assertions for properties *)
Definition SL_1_TA : top_assertion (derives_assertion SL_1).
Proof.
  repeat apply LAForAll.
  apply LAIf; first by apply LAAnd; apply LACorrect.
  apply LAEntails; first by apply LAEventOn with (dp := [::]).
  by apply LAAlways, LAEventually, LAEventOn with (dp := [::]).
Defined.

Definition SL_2_TA : top_assertion (derives_assertion SL_2).
Proof.
  repeat apply LAForAll.
  by apply LAPrecededBy; apply LAEventOn with (dp := [::]).
Defined.
