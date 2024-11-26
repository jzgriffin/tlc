(* TLC in Coq
 *
 * Module: tlc.component.stubborn_link_2
 * Purpose: Contains the local specification of the stubborn link SL_2 property.
 *)

Require Import mathcomp.ssreflect.eqtype.
Require Import mathcomp.ssreflect.seq.
Require Import mathcomp.ssreflect.ssrbool.
Require Import mathcomp.ssreflect.ssreflect.
Require Import mathcomp.ssreflect.ssrnat.
Require Import tlc.component.component.
Require Import tlc.component.stubborn_link.
Require Import tlc.logic.all_logic.
Require Import tlc.semantics.all_semantics.
Require Import tlc.syntax.all_syntax.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* No-forge
 * If a node n delivers a message m with sender n', then m was previously sent
 * to n by n' *)
Theorem SL_2 Delta : Context Delta [::] ||- stubborn_link, {-A
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
      (S := {-A forall: (* s *) on n', (n, m) \in $$0 -})
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

(* Top assertion for SL_2 *)
Definition SL_2_TA Delta : top_assertion (derives_assertion (SL_2 Delta)).
Proof.
  repeat apply LAForAll.
  by apply LAPrecededBy; apply LAEventOn with (dp := [::]).
Defined.
