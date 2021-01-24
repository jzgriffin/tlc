(* TLC in Coq
 *
 * Module: tlc.component.perfect_link_3
 * Purpose: Contains the local specification of the perfect link PL_3 property.
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

(* No forge
 * If a node n delivers a message m with sender n', then m was previously sent
 * to n by node n'.
 *)
Theorem PL_3 Delta : Context Delta [::] ||- perfect_link, {-A
  forall: forall: forall: (* n, n', m *)
  $$2 \in UCorrect /\ $$1 \in UCorrect ->
  on $$2, event[]<- CPLDeliver ' $$1 ' $$0 <~
  on $$1, event[]-> CPLSend ' $$2 ' $$0
 -}.
Proof.
  dforall n; dforall n'; dforall m; dif; dsplitp.

  (* By OI' *)
  dhave {-A
    on n, event[]<- CPLDeliver ' n' ' m <~
    on n, CPLDeliver ' n' ' m \in Fois /\ self-event
  -}.
  {
    duse DPOI'; dforallp n; dforallp {-t CPLDeliver ' n' ' m -}.
    eapply DSCut; first (by repeat dclear; apply DTL123 with
      (A := {-A self-event /\ on n, CPLDeliver ' n' ' m \in Fois -}));
      dtsubstposp.
    eapply DSCut; first (by repeat dclear; apply DTAndComm with
      (A1 := {-A self-event -})
      (A2 := {-A on n, CPLDeliver ' n' ' m \in Fois -}));
      dtsubstp_l.
    by eapply DSCut; first (by repeat dclear; apply DTAndAssoc with
      (A1 := {-A Fn = n -})
      (A2 := {-A CPLDeliver ' n' ' m \in Fois -})
      (A3 := {-A self-event -}));
      dtsubstp_l.
  }

  (* By InvL *)
  dhave {-A
    on n, CPLDeliver ' n' ' m \in Fois /\ self-event =>>
    exists: (* c *) on n, event[0]<- CSLDeliver ' n' ' ($$0, m)
  -}.
  {
    repeat dclear.
    eapply DSCut; first by apply DPInvL with
      (A := {-A
        on n, CPLDeliver ' n' ' m \in Fois ->
        exists: (* c *) on n, event[0]<- CSLDeliver ' n' ' ($$0, m)
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
        dif; dsplitp.
      - dexists e_c; dsplit; first (by dassumption); dclear.
        dswap; dtsubstep_l; dswap; dclear.
        by dpmembersingletonp; dtinjectionp; repeat (dsplitp; dswap);
        repeat (dtgenp; dtsubste_l; dautoeq; dclear).
      - by dclear; dswap; dtsubstep_l; dpmembernilp.
    }

    (* periodic *)
    difp.
    {
      dif; dsplitp; dswap; dsimplp.
      dtinjectionp; repeat dsplitp; do 2 dclear.
      dif; dsplitp; dclear.
      by dswap; dtgenp; dtsubstep_l; dpmembernilp.
    }

    dtmergeentailsifp.
    eapply DSCut; first (by repeat dclear; apply DTAndComm with
      (A1 := {-A self-event -})
      (A2 := {-A on n, CPLDeliver ' n' ' m \in Fois -}));
      dtsubstp_l.
    by eapply DSCut; first (by repeat dclear; apply DTAndAssoc with
      (A1 := {-A Fn = n -})
      (A2 := {-A CPLDeliver ' n' ' m \in Fois -})
      (A3 := {-A self-event -}));
      dtsubstp_l.
  }

  (* By lemma 99 on (1) and (2) *)
  (* NOTE: Rewriting is easier. *)
  dtsubstposp.

  (* By rule OR' *)
  dhave {-A
    forall: (* c *)
    on n', event[0]-> CSLSend ' n ' ($$0, m) <~
    on n', (0, CSLSend ' n ' ($$0, m)) \in Fors /\ self-event
  -}.
  {
    dforall c.
    duse DPOR'; dforallp n'; dforallp {-t 0 -}; dforallp {-t CSLSend ' n ' (c, m) -}.
    eapply DSCut; first (by repeat dclear; apply DTL123 with
      (A := {-A self-event /\ on n', (0, CSLSend ' n ' (c, m)) \in Fors -}));
      dtsubstposp.
    eapply DSCut; first (by repeat dclear; apply DTAndComm with
      (A1 := {-A self-event -})
      (A2 := {-A on n', (0, CSLSend ' n ' (c, m)) \in Fors -}));
      dtsubstp_l.
    by eapply DSCut; first (by repeat dclear; apply DTAndAssoc with
      (A1 := {-A Fn = n' -})
      (A2 := {-A (0, CSLSend ' n ' (c, m)) \in Fors -})
      (A3 := {-A self-event -}));
      dtsubstp_l.
  }

  (* By rule InvL *)
  dhave {-A
    forall: (* c *)
    on n', (0, CSLSend ' n ' ($$0, m)) \in Fors /\ self-event =>>
    on n', event[]-> CPLSend ' n ' m
  -}.
  {
    repeat dclear.
    dforall c.
    eapply DSCut; first by apply DPInvL with
      (A := {-A
        on n', (0, CSLSend ' n ' (c, m)) \in Fors ->
        on n', event[]-> CPLSend ' n ' m
      -});
      [by dautoclosed | by repeat constructor].

    (* request *)
    difp.
    {
      dforall e; dif; dsplitp; dswap; dsimplp.
      dcase {-t ? e -}; dexistsp e_m; dexistsp e_n'; dtgenp;
        dtsubstep_l; dsimplp;
        dswap; dxchg 1 2; dtsubstep_l; dswap; dclear; dswap.
      dcase {-t ? Fs ' ? Fn -}; dexistsp s_r; dexistsp s_c; dtgenp;
        dtsubstep_l; dswap; dclear; dsimplp.
      dtinjectionp; repeat dsplitp; dclear; dswap; dclear.

      dif; dsplitp; dsplit; first (by dassumption); dclear.
      dswap; dtgenp; dtsubstep_l; dswap; dclear.
      by dpmembersingletonp; dtinjectionp; repeat (dsplitp; dswap);
      do 2 (dtgenp; dtsubste_l; dautoeq; dclear; dclear).
    }

    (* indication *)
    difp.
    {
      dforall i; dforall e; dif; dsplitp; dswap; dsimplp.
      dcase {-t (? i, ? e) -}; dexistsp e_m; dexistsp e_c; dexistsp e_n; dtgenp;
        dtsubstep_l; dswap; dclear; dsimplp.
      dcase {-t ? Fs ' ? Fn -}; dexistsp s_r; dexistsp s_c; dtgenp;
        dtsubstep_l; dswap; dclear; dsimplp.
      dcase {-t FCount ' (? e_n, ? e_c) ' ? s_r == 0 -}; dorp; dtgenp;
        dtsubstep_l; dswap; dclear; dsimplp;
        dtinjectionp; repeat dsplitp;
        dclear; dswap; dclear; dtgenp; dtsubste_l; dclear;
        dif; dsplitp; dclear;
        by dpmembernilp.
    }

    (* periodic *)
    difp.
    {
      dif; dsplitp; dswap; dsimplp.
      dtinjectionp; repeat dsplitp; dclear; dswap; dclear.
      dif; dsplitp; dclear.
      by dswap; dtgenp; dtsubstep_l; dpmembernilp.
    }

    dtmergeentailsifp.
    eapply DSCut; first (by repeat dclear; apply DTAndComm with
      (A1 := {-A self-event -})
      (A2 := {-A on n', (0, CSLSend ' n ' (c, m)) \in Fors -}));
      dtsubstp_l.
    by eapply DSCut; first (by repeat dclear; apply DTAndAssoc with
      (A1 := {-A Fn = n' -})
      (A2 := {-A (0, CSLSend ' n ' (c, m)) \in Fors -})
      (A3 := {-A self-event -}));
      dtsubstp_l.
  }

  (* By lemma 99 on (1) and (2) *)
  (* NOTE: Rewriting is easier. *)
  dtsubstposp.

  (* By lemma 88 on (3), SL_2', and (6) *)
  duse PL_SL_2.
  dxchg 1 2; dtsubstposp.
  dswap; dtsubstposp.
  eapply DSCut; first (by repeat dclear; apply DTL83_1 with
    (A := {-A on n', event[]-> CPLSend ' n ' m -}));
    dtsubstp_r.
  eapply DSCut; first (by repeat dclear; apply DTL127_3 with
    (A := {-A on n', event[]-> CPLSend ' n ' m -}));
    dtsubstp_r.
  eapply DSCut; first (by repeat dclear; apply DTL83_1 with
    (A := {-A exists: on n', event[]-> CPLSend ' n ' m -}));
    dtsubstp_r.
  by eapply DSCut; first (by repeat dclear; apply DTExistsConstant with
    (A := {-A on n', event[]-> CPLSend ' n ' m -}); first by dautoclosed);
    dtsubstp_r.
Qed.
