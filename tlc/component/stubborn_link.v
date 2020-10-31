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
Theorem SL_2 : empty_context ||- stubborn_link, {-A
  forall: forall: forall: (* 2:n, 1:n', 0:m *)
  on $$2, event[]<- {-t CSLDeliver ' $$1 ' $$0 -} <~
  on $$1, event[]-> {-t CSLSend ' $$2 ' $$0 -}
-}.
Proof.
  (* Introduce context *)
  set C := stubborn_link; rewrite -/C /empty_context.
  dforall n; dforall n'; dforall m; dclean.

  (* By OI' *)
  dhave {-A
    on n, event[]<- CSLDeliver ' n' ' m =>>
    eventuallyp (self-event /\ on n, (CSLDeliver ' n' ' m \in Fois))
  -}.
  {
    (* Instantiate OI' *)
    duse DPOI'; dforallp n; dforallp {-t CSLDeliver ' n' ' m -}; dclean.

    eapply DARewriteIfP; first by apply DTL123 with (A := {-A
      self-event /\ on n, (CSLDeliver ' n' ' m \in Fois) -}).
    by dclean.
  }

  (* By InvL *)
  dhave {-A
    self-event /\ on n, (CSLDeliver ' n' ' m \in Fois) =>>
    on n, event[0]<- CFLDeliver ' n' ' m
  -}.
  {
    dclear. (* dclean up the context *)

    (* Instantiate InvL *)
    eapply DSCut; first by apply DSEmptyContext; apply DPInvL with (A := {-A
        on n, (CSLDeliver ' n' ' m \in Fois) ->
        on n, event[0]<- CFLDeliver ' n' ' m
      -}); first by repeat constructor.

    (* Prove for requests *)
    difp.
      (* Obtain the first contradictory premise *)
      dforall e; dclean.
      dif; dsplitp; dswap; dsimplp.
      ddestructp (fun t => {-A (Fs' ' Fn, Fors, Fois) = t -});
        dexistsp m_; dexistsp n'_; dsplitp; dswap;
        dsubstp; dsimplp.
      ddestructpairp; do 2 dsplitp.
      do 2 dclear; do 2 (dswap; dclear). (* dclean up the context *)

      (* Obtain the second contradictory premise *)
      by dif; dsplitp; dclear; dsubstp; dsimplp.


    (* Prove for indications *)
    difp.
      dforall i; dforall e; dclean.
      dif; dsplitp; dswap; dsimplp.
      ddestructp (fun t => {-A (Fs' ' Fn, Fors, Fois) = t -});
        dexistsp m_; dexistsp n'_; dsplitp; dswap;
        dsubst; dsimplp.
      ddestructpairp; do 2 dsplitp.
      dif; dsplitp.
      dsplit; first by dhead.
      dswap; do 3 (dswap; drotate 1); dsubstp.
      din_cons_pl; dclean.
      dorp; last by dsimplp.
      eapply DSEqualEvent; dsplitp.
      dsubstc; dclear; dsubstc; dclear;
        distinguish_variables; rewrite eq_refl.
      dclear; ddestructpairp; dsplitp; drotate 2; do 3 (dswap; dclear).
      by do 2 (dsubstp; dswap; dclear);
        distinguish_variables; rewrite eq_refl.

    (* Prove for periodics *)
    difp.
      (* Obtain the first contradictory premise *)
      dif; dsplitp; dswap; dsimplp.
      ddestructpairp; repeat dsplitp.
      do 2 dclear; (dswap; dclear). (* dclean up the context *)

      (* Obtain the second contradictory premise *)
      by dif; dsplitp; dclear; dsubstp; dsimplp.

    eapply DARewriteIffPL; first by apply DSMergeIf with
      (Ap1 := {-A self-event -})
      (Ap2 := {-A on n, (CSLDeliver ' n' ' m \in Fois) -})
      (Ac := {-A on n, event[0]<- CFLDeliver ' n' ' m -}).
    by dclean.
  }

  (* From (1) and (2) *)
  dhave {-A
    on n, event[]<- CSLDeliver ' n' ' m <~
    on n, event[0]<- CFLDeliver ' n' ' m
  -}.
  {
    drotate 1; eapply DARewriteEntailsP; first by dhead.
    by dclean.
  }

  (* By NForge *)
  dhave {-A
    on n, event[0]<- CFLDeliver ' n' ' m <~
    on n', event[0]-> CFLSend ' n ' m
  -}.
  {
    (* Instantiate NForge *)
    by duse DPNForge;
      dforallp n'; dforallp n; dforallp m; dforallp 0.
  }

  (* By lemma 85 on (3) and (4) *)
  dhave {-A
    on n, event[]<- CSLDeliver ' n' ' m <~
    on n', event[0]-> CFLSend ' n ' m
  -}.
  {
    by eapply DTL85; first by drotate 1; dhead.
  }

  (* By OR' *)
  dhave {-A
    on n', event[0]-> CFLSend ' n ' m =>>
    eventuallyp (self-event /\ on n',
      ((0, CFLSend ' n ' m) \in Fors))
  -}.
  {
    (* Instantiate OR' *)
    duse DPOR';
      dforallp n'; dforallp 0; dforallp {-t CFLSend ' n ' m -}; dclean.

    eapply DARewriteIfP; first by apply DTL123 with (A := {-A
      self-event /\ on n', ((0, CFLSend ' n ' m) \in Fors) -}).
    by dclean.
  }

  (* By InvSA *)
  dhave {-A
    self-event /\ on n', ((n, m) \in Fs ' n') =>>
    eventuallyp^ on n', event[]-> CSLSend ' n ' m
  -}.
  {
    do 6 dclear. (* dclean up the context *)

    (* Instantiate InvSA *)
    eapply DSCut; first by apply DPInvSA with
      (S0 := {-A forall: (* 0:ts *) on n', ((n, m) \in $$0) -})
      (A := {-A event[]-> CSLSend ' n ' m -});
      [by auto_is_closed | by repeat econstructor | by repeat econstructor].
    dforallp n'; dclean.

    (* Prove for initialization *)
    difp.
      dsimpl.
      by dnotc; dsplitp; dassumption.

    (* Prove for requests *)
    difp.
      dforall e; dsimpl.
      dif; dsplitp; dsplitp; do 2 (dswap; dsplitp).
      dsplit; first by dassumption.
      dsplit; first by dassumption.
      drotate 4; dsplitp.
      ddestructp (fun t => {-A (Fs' ' Fn, Fors, Fois) = t -});
        dexistsp m_; dexistsp n_; dsplitp;
        dswap; dsubstp; dsimplp;
        ddestructpairp; repeat dsplitp.
      drotate 4; dsplitp.
      drotate 5; dswap; dsubstp.
      do 5 (dswap; drotate 1); dswap; dsubstp.
      dsplitp; dclear.
      do 8 (dswap; drotate 1); dswap.
      duse DSDistributeNand; dsplitp; dswap; dclear.
      eapply DSModusPonensP; first by dhead.
      dswap; dclear; dorp.
        do 5 (dswap; drotate 1); dsubstp.
        dnotp; first by apply DAPEqual.
      dswap; din_union_pr; dclean.
      dorp; first by dswap; dnotp.
      din_cons_pl; dclean.
      dorp; last by dsimplp.
      eapply DSEqualEvent.
      do 8 (dswap; drotate 1); dsplitp; do 2 (dsubstc; dclear);
        distinguish_variables; rewrite eq_refl.
      do 3 (dswap; drotate 1); dswap; dsubstc; distinguish_variables.
      by dassumption.

    (* Prove for indications *)
    difp.
      dforall i; dforall e; dsimpl.
      dif; dsplitp; dswap; dsplitp.
      ddestructp (fun t => {-A (Fs' ' Fn, Fors, Fois) = t -});
        dexistsp m_; dexistsp n_; dsplitp;
        dswap; dsubstp; dsimplp;
        ddestructpairp; repeat dsplitp.
      drotate 5; dsplitp.
      dswap; drotate 1; dswap; dsubstp.
      do 4 (dswap; drotate 1); dswap; dsubstp; dsplitp.
      by dnotp.

    (* Prove for periodics *)
    difp.
      dsimpl; dif; dsplitp; dswap; dsplitp.
      ddestructpairp; repeat dsplitp.
      do 2 (dswap; dclear); dswap.
      drotate 2; dsplitp; dswap; dclear; drotate 2; dsubstp.
      dswap; drotate 2; dsubstp; dswap; dclear; dsplitp.
      by dnotp; dsubstp.

    by dsimplp.
  }

  (* By InvL *)
  dhave {-A
    self-event /\ on n', ((n, m) \in Fs' ' n') =>>
    (self-event /\ on n', (((n, m) \in Fs ' n')) \/
      on n', event[]-> CSLSend ' n ' m)
  -}.
  {
    repeat dclear. (* dclean up the context *)

    (* Instantiate InvL *)
    eapply DSCut; first by apply DSEmptyContext; apply DPInvL with (A := {-A
        on n', ((n, m) \in Fs' ' n') ->
        (on n', ((n, m) \in Fs ' n') \/
          on n', event[]-> CSLSend ' n ' m) -});
      first by repeat constructor.

    (* Prove for requests *)
    difp.
      dforall e; dclean.
      dif; dsplitp; dsplitp; dswap; dsplitp.
      drotate 3; dsubstp; dsimplp.
      ddestructp (fun t => {-A (Fs' ' Fn, Fors, Fois) = t -});
        dexistsp m_; dexistsp n_; dclean; dsplitp;
        dswap; dsubstp; dsimplp;
        ddestructpairp; repeat dsplitp.

      dif; dsplitp.
      dswap; drotate 1; dswap; dsubstp.
      do 7 (dswap; drotate 1); dswap; dsubstp.
      din_union_pr; dclean; dswap; dclear; dorp;
        first by dleft; dsplit; dassumption.
      dright; dsplit; first by dassumption.
      din_cons_pl; dclean; dorp; last by dsimplp.
      ddestructpairp; dsplitp; dsubstc; dclear; dsubstc;
        dclear; distinguish_variables; rewrite eq_refl.
      repeat (dsplit; first by dassumption).
      by drotate 5; dsubstc; dassumption.

    (* Prove for indications *)
    difp.
      dforall i; dforall e; dclean.
      dif; dsplitp; dsplitp; dswap; dsplitp.
      drotate 3; dsimplp.
      ddestructp (fun t => {-A (Fs' ' Fn, Fors, Fois) = t -});
        dexistsp m_; dexistsp n_; dclean; dsplitp;
        dswap; dsubstp; dsimplp;
        ddestructpairp; repeat dsplitp.

      dif; dsplitp.
      dswap; drotate 1; dswap; dsubstp.
      dleft; dsplit; first by dassumption.
      by do 7 (dswap; drotate 1); dswap; dsubstp.

    (* Prove for periodics *)
    difp.
      dif; dsplitp; dsplitp; dswap; dsplitp.
      drotate 3; dsimplp.

      dif; dsplitp; dleft; dsubstc.
      dsplit; first by eapply DAPEqual.

      drotate 2; do 3 (dswap; dclear); dsubstp.
      ddestructpairp; do 2 dsplitp; do 3 (dswap; dclear); dswap; dsubstp.
      by dassumption.

    eapply DARewriteIffPL; first by apply DSMergeIf with
      (Ap1 := {-A self-event -})
      (Ap2 := {-A on n', ((n, m) \in Fs' ' n') -})
      (Ac := {-A on n', (((n, m) \in Fs ' n')) \/
        on n', event[]-> CSLSend ' n ' m -}).
    eapply DARewriteIffPL; first by apply DSIfAndIntroduce with
      (Apl := {-A self-event -})
      (Apr := {-A on n', ((n, m) \in Fs' ' n') -})
      (Ac := {-A on n', ((n, m) \in Fs ' n') \/
        on n', event[]-> CSLSend ' n ' m -}).
    eapply DARewriteIffPL; first by apply DSOrDistributesAnd with
      (Al := {-A on n', ((n, m) \in Fs ' n') -})
      (Ar := {-A on n', event[]-> CSLSend ' n ' m -})
      (A := {-A self-event -}).
    eapply DARewriteIffPL; first by apply DSAndComm with
      (Acl := {-A Fn = n' -})
      (Acr := {-A event[]-> CSLSend ' n ' m -}).
    eapply DARewriteIffPR; first by apply DSAndAssociative with
      (Al := {-A self-event -})
      (Am := {-A event[]-> CSLSend ' n ' m -})
      (Ar := {-A Fn = n' -}).
    eapply DARewriteIffPL; first by apply DSAndComm with
      (Acl := {-A self-event -})
      (Acr := {-A event[]-> CSLSend ' n ' m -}).
    dclean; rewrite !andbF /=; dclean.
    eapply DARewriteIffPL; first by duse DPTopRequestSelfEliminate;
      dforallp {-t CSLSend ' n ' m -}; dhead.
    eapply DARewriteIffPL; first by apply DSAndComm with
      (Acl := {-A event[]-> CSLSend ' n ' m -})
      (Acr := {-A Fn = n' -}).
    by dclean.
  }

  (* By InvL *)
  dhave {-A
    self-event /\ on n', ((0, CFLSend ' n ' m) \in Fors) =>>
    self-event /\ on n', ((n, m) \in Fs' ' n')
  -}.
  {
    repeat dclear. (* dclean up the context *)

    (* Instantiate InvL *)
    eapply DSCut; first by apply DSEmptyContext; apply DPInvL with (A := {-A
        on n', ((0, CFLSend ' n ' m) \in Fors) ->
        on n', ((n, m) \in Fs' ' n')
      -}); first by repeat constructor.

    (* Prove for requests *)
    difp.
      dforall e; dclean.
      dif; dsplitp; dsplitp; dswap; dsplitp.
      drotate 3; dsubstp; dsimplp.
      ddestructp (fun t => {-A (Fs' ' Fn, Fors, Fois) = t -});
        dexistsp m_; dexistsp n_; dclean; dsplitp;
        dswap; dsubstp; dsimplp;
        ddestructpairp; repeat dsplitp.

      dif; dsplitp; dsplit; first by dhead.
      dswap; do 2 (dswap; drotate 1); dsubstp.
      din_cons_pl; dclean; dorp; last by dsimplp.
      ddestructpairp; dsplitp; dclear; apply DSEqualEvent.

      do 6 (dswap; dclear); drotate 1; dswap; dsubstp; dswap; dclear.
      dswap; dsplitp; dsubstc; dclear; dsubstc; dclear;
        distinguish_variables; rewrite eq_refl /eq_op /=; distinguish_variables.
      dsubstc.
      duse DAPInUnion;
        dforallp {-t Fs ' n' -};
        dforallp {-t [(n_, m_)] -};
        dforallp {-t (n_, m_) -};
        dclean;
        dsplitp; dswap; dclear.
      by difp; first by dright; dsimpl.

    (* Prove for indications *)
    difp.
      dforall i; dforall e; dclean.
      dif; dsplitp; dsplitp; dswap; dsplitp.
      drotate 3; dsubstp; dsimplp.
      ddestructp (fun t => {-A (Fs' ' Fn, Fors, Fois) = t -});
        dexistsp m_; dexistsp n_; dclean; dsplitp;
        dswap; dsubstp; dsimplp;
        ddestructpairp; repeat dsplitp.

      dif; dsplitp; dsplit; first by dhead.
      by dclear; dswap; drotate 1; dsubstp; dsimplp.

    (* Prove for periodics *)
    difp.
      dif; dsplitp; dswap; dsimplp.
      set tf := {-t fun: match: $$0 with:
        { ($, $) -> (0, CFLSend ' $$0 ' $$1) } -}.
      ddestructpairp; do 2 dsplitp.
      dif; dsplitp; dsplit; first by dhead.
      dswap; dsubstp; drotate 2; dsubst; drotate 5.
      duse DAPInMap;
        dforallp tf; dforallp {-t (n, m) -}; dforallp {-t Fs ' Fn -}; dclean.
      dsplitp; dclear; dsimplp; difp; first by
        dclear; dswap; drotate 4; dsubstp.
      dswap; drotate 1; dswap.
      dhave {-A Fs ' Fn = Fs' ' Fn -}; first by duse DAPEqualSymmetric;
        dforallp {-t Fs' ' Fn -}; dforallp {-t Fs ' Fn -}; dclean;
        dsplitp; difp; dassumption.
      by dswap; dclear; dswap; dsubstp; do 5 (dswap; dclear); dsubstp.

    eapply DARewriteIffPL; first by apply DSMergeIf with
      (Ap1 := {-A self-event -})
      (Ap2 := {-A on n', ((0, CFLSend ' n ' m) \in Fors) -})
      (Ac := {-A on n', ((n, m) \in Fs' ' n') -}).
    eapply DARewriteIffPL; first by apply DSIfAndIntroduce with
      (Apl := {-A self-event -})
      (Apr := {-A on n', ((0, CFLSend ' n ' m) \in Fors) -})
      (Ac := {-A on n', ((n, m) \in Fs' ' n') -}).
    by dclean.
  }

  (* By (8) and (9) *)
  dhave {-A
    self-event /\ on n', ((0, CFLSend ' n ' m) \in Fors) =>>
    (self-event /\ on n', ((n, m) \in Fs ' n')) \/
      on n', event[]-> CSLSend ' n ' m
  -}.
  {
    eapply DARewriteEntailsP; first by dhead.
    by dclean; rewrite /eq_op /= andbF.
  }

  (* By (6) and (10) *)
  dhave {-A
    on n', event[0]-> CFLSend ' n ' m <~
    self-event /\ on n', ((n, m) \in Fs ' n') \/
    on n', event[]-> CSLSend ' n ' m
  -}.
  {
    drotate 4; eapply DARewriteEntailsP; first by drotate 5; dhead.
    by dclean.
  }

  (* By (7) and (11) *)
  dhave {-A
    on n', event[0]-> CFLSend ' n ' m <~
    on n', event[]-> CSLSend ' n ' m
  -}.
  {
    eapply DARewriteEntailsP; first by drotate 3; dhead.
    dclean.
    eapply DARewriteIffPL; first by apply DSOrComm with
      (Acl := {-A eventuallyp^ on n', event[]-> CSLSend ' n ' m -})
      (Acr := {-A on n', event[]-> CSLSend ' n ' m -}).
    dclean.
    eapply DARewriteCongruentCL; first by apply DTL83_1 with
      (A := {-A on n', event[]-> CSLSend ' n ' m -}).
    by dclean.
  }

  (* From (5) and (12) *)
  dhave {-A
    on n, event[]<- CSLDeliver ' n' ' m <~
    eventuallyp on n', event[]-> CSLSend ' n ' m
  -}.
  {
    drotate 7; eapply DARewriteEntailsP; first by drotate 4; dhead.
    by dclean; rewrite /eq_op /= andbF.
  }

  (* By lemma 83 on (9) *)
  (* NOTE: This line is missing from the paper proof *)
  dhave {-A
    on n, event[]<- CSLDeliver ' n' ' m <~
    on n', event[]-> CSLSend ' n ' m
  -}.
  {
    eapply DARewriteCongruentCL; first by apply DTL83_1 with
      (A := {-A on n', event[]-> CSLSend ' n ' m -}).
    by dclean.
  }

  by [].
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
