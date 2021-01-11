(* TLC in Coq
 *
 * Module: tlc.component.stubborn_link_1
 * Purpose: Contains the local specification of the stubborn link SL_1 property.
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

(* Stubborn delivery
 * If a correct node n sends a message m to a correct node n', then n'
 * delivers m infinitely often *)
Theorem SL_1 Delta : Context Delta [::] ||- stubborn_link, {-A
  forall: forall: forall: (* n, n', m *)
  $$2 \in UCorrect /\ $$1 \in UCorrect ->
  on $$2, event[]-> CSLSend ' $$1 ' $$0 =>>
  always eventually on $$1, event[]<- CSLDeliver ' $$2 ' $$0
-}.
Proof.
  set C := stubborn_link.

  dforall n; dforall n'; dforall m.
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

(* Top assertion for SL_1 *)
Definition SL_1_TA Delta : top_assertion (derives_assertion (SL_1 Delta)).
Proof.
  repeat apply LAForAll.
  apply LAIf; first by apply LAAnd; apply LACorrect.
  apply LAEntails; first by apply LAEventOn with (dp := [::]).
  by apply LAAlways, LAEventually, LAEventOn with (dp := [::]).
Defined.
