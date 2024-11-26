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
  dforall n; dforall n'; dforall m; dforall c; dforall c'; dif.

  (* This proof is simpler to write without the self operator *)
  match goal with
  | |- Context _ _ ||- _, {-A self ?A_ -} =>
    eapply DSCut; first (by repeat dclear; apply DPSInv_2 with (A := A_))
  end; difp; last by [].
  rewrite /restrict_assertion /=; dclean.

  dtmergeif; dtsubst_r; dclear.
  match goal with
  | |- context[ {-A always^ (?A1_ /\ ?A2_ /\ ?A3_ -> _) -} ] =>
    eapply DSCut; first (by repeat dclear; apply DTAndAssoc with
      (A1 := A1_) (A2 := A2_) (A3 := A3_))
  end; dtsubst_l; dclear.
  dhave {-A
    (on n, event[0]<- CSLDeliver ' n' ' (c, m)) <->
    (self-event /\ on n, event[0]<- CSLDeliver ' n' ' (c, m))
  -}.
  {
    dsplit; dif.
    - dsplit; last by [].
      dsplitp; dclear.
      dleft; dexists {-t 0 -}; dsplit; dsplitp; first by [].
      by dclear; dsplitp.
    - by dsplitp; dclear.
  }
  dtgenp; dclean; dtsubst_l; dclear.

  (* c *)
    (* By SL_2 *)
    duse PL_SL_2; dforallp n; dforallp n'; dforallp {-t (c, m) -}.

    (* By OR' *)
    duse DPOR'; dforallp n'; dforallp {-t 0 -}; dforallp {-t CSLSend ' n ' (c, m) -}.
    eapply DSCut; first (by repeat dclear; apply DTL123 with
      (A := {-A self-event /\ (on n', (0, CSLSend ' n ' (c, m)) \in Fors) -}));
      dtsubstposp.

    (* By InvL *)
    eapply DSCut; first (by repeat dclear; apply DPInvL with
      (A := {-A
        (on n', (0, CSLSend ' n ' (c, m)) \in Fors) ->
        (on n', event[]-> CPLSend ' n ' m) /\
        (Fs' ' n').1 = c
      -});
      [by dautoclosed | repeat constructor]).
    (* request *)
    difp.
    {
      repeat dclear; dforall e; dsimpl.
      dif; dsplitp; dswap.
      dif; dsplitp; dtgenp.
      dxchg 1 2; dtsubstep_l; dswap; dtsubste_l; dclear.
      dcase {-t ? e -}; dexistsp e_m; dexistsp e_n'; dtgenp;
        dtsubstep_l; dautoeq; dsimplp; dxchg 0 3; dswap;
        dtsubstep_l; dautoeq; dswap; dclear; dxchg 0 2.
      dcase {-t ? Fs ' ? n' -}; dexistsp s_r; dexistsp s_c; dtgenp;
        dtsubstep_l; dsimplp; dswap;
        dtsubste_l; dclear.
      dtinjectionp; repeat dsplitp.
      dsplit; first dsplit.
      - by repeat dclear; exact: DPEqual.
      - dclear; dtgenp; dswap; dclear; dtsubstep_l; dswap; dclear.
        dpmembersingletonp; dtinjectionp; repeat (dsplitp; dswap).
        dtgenp; dtsubste_l; dautoeq; dclear.
        dclear.
        dtgenp; dtsubste_l; dautoeq; dclear.
        by dswap.
      - dtgenp; dtsubste_l; dautoeq; dclear; dsimpl.
        dswap; dclear; dtgenp; dtsubstep_l; dswap; dclear.
        dpmembersingletonp; dtinjectionp; repeat (dsplitp; dswap).
        dclear; dtgenp; dtsubste_l; dautoeq.
        by repeat dclear; exact: DPEqual.
    }
    (* indication *)
    difp.
    {
      repeat dclear; dforall i; dforall e; dsimpl.
      dif; dsplitp; dswap.
      dif; dsplitp; dtgenp.
      dxchg 1 2; dtsubstep_l; dswap; dtsubste_l; dclear.
      dcase {-t (? i, ? e) -}; dexistsp e_m; dexistsp e_c; dexistsp e_n;
        dtinjectionp.
      dsplitp; do 2 (dtgenp; dswap); dxchg 1 2.
      dtsubstep_l; dautoeq; dswap; dxchg 1 4.
      dtsubstep_l; dautoeq; dswap; dclear; dswap.
      dtsubstep_l; dautoeq; dswap; dxchg 1 3.
      dtsubstep_l; dautoeq; dswap; dclear.
      dcase {-t ? Fs ' ? n' -}; dexistsp s_r; dexistsp s_c; dtgenp;
        dtsubstep_l; dswap; dclear; dsimplp.
      dcase {-t FCount ' (? e_n, ? e_c) ' ? s_r == 0 -}; dorp; dtgenp;
        dtsubstep_l; dswap; dclear; dsimplp;
        dtinjectionp; repeat dsplitp; dclear; dtgenp;
        dswap; dclear;
        dtsubstep_l;
        by dpmembernilp.
    }
    (* periodic *)
    difp.
    {
      repeat dclear; dsimpl.
      dif; dsplitp; dclear.
      dif; dsplitp; dclear.
      dswap; dtinjectionp; repeat dsplitp.
      dclear; dswap; dclear; dtgenp.
      by dtsubstep_l; dpmembernilp.
    }
    dtmergeentailsifp.

    (* By lemma 89 and lemma 99 on (1), (2), and (3) *)
    dxchg 0 2; dswap; dtsubstposp.
    dswap; dtsubstposp.
    eapply DSCut; first (by repeat dclear; apply DTL83_1 with
      (A := {-A (on n', event[]-> CPLSend ' n ' m) /\ (Fs' ' n').1 = c -}));
      dtsubstp_r.

  (* c' *)
    (* By SL_2 *)
    duse PL_SL_2; dforallp n; dforallp n'; dforallp {-t (c', m) -}.

    (* By OR' *)
    duse DPOR'; dforallp n'; dforallp {-t 0 -}; dforallp {-t CSLSend ' n ' (c', m) -}.
    eapply DSCut; first (by repeat dclear; apply DTL123 with
      (A := {-A self-event /\ (on n', (0, CSLSend ' n ' (c', m)) \in Fors) -}));
      dtsubstposp.

    (* By InvL *)
    eapply DSCut; first (by repeat dclear; apply DPInvL with
      (A := {-A
        (on n', (0, CSLSend ' n ' (c', m)) \in Fors) ->
        (on n', event[]-> CPLSend ' n ' m) /\
        (Fs' ' n').1 = c'
      -});
      [by dautoclosed | repeat constructor]).
    (* request *)
    difp.
    {
      repeat dclear; dforall e; dsimpl.
      dif; dsplitp; dswap.
      dif; dsplitp; dtgenp.
      dxchg 1 2; dtsubstep_l; dswap; dtsubste_l; dclear.
      dcase {-t ? e -}; dexistsp e_m; dexistsp e_n'; dtgenp;
        dtsubstep_l; dautoeq; dsimplp; dxchg 0 3; dswap;
        dtsubstep_l; dautoeq; dswap; dclear; dxchg 0 2.
      dcase {-t ? Fs ' ? n' -}; dexistsp s_r; dexistsp s_c; dtgenp;
        dtsubstep_l; dsimplp; dswap;
        dtsubste_l; dclear.
      dtinjectionp; repeat dsplitp.
      dsplit; first dsplit.
      - by repeat dclear; exact: DPEqual.
      - dclear; dtgenp; dswap; dclear; dtsubstep_l; dswap; dclear.
        dpmembersingletonp; dtinjectionp; repeat (dsplitp; dswap).
        dtgenp; dtsubste_l; dautoeq; dclear.
        dclear.
        dtgenp; dtsubste_l; dautoeq; dclear.
        by dswap.
      - dtgenp; dtsubste_l; dautoeq; dclear; dsimpl.
        dswap; dclear; dtgenp; dtsubstep_l; dswap; dclear.
        dpmembersingletonp; dtinjectionp; repeat (dsplitp; dswap).
        dclear; dtgenp; dtsubste_l; dautoeq.
        by repeat dclear; exact: DPEqual.
    }
    (* indication *)
    difp.
    {
      repeat dclear; dforall i; dforall e; dsimpl.
      dif; dsplitp; dswap.
      dif; dsplitp; dtgenp.
      dxchg 1 2; dtsubstep_l; dswap; dtsubste_l; dclear.
      dcase {-t (? i, ? e) -}; dexistsp e_m; dexistsp e_c; dexistsp e_n;
        dtinjectionp.
      dsplitp; do 2 (dtgenp; dswap); dxchg 1 2.
      dtsubstep_l; dautoeq; dswap; dxchg 1 4.
      dtsubstep_l; dautoeq; dswap; dclear; dswap.
      dtsubstep_l; dautoeq; dswap; dxchg 1 3.
      dtsubstep_l; dautoeq; dswap; dclear.
      dcase {-t ? Fs ' ? n' -}; dexistsp s_r; dexistsp s_c; dtgenp;
        dtsubstep_l; dswap; dclear; dsimplp.
      dcase {-t FCount ' (? e_n, ? e_c) ' ? s_r == 0 -}; dorp; dtgenp;
        dtsubstep_l; dswap; dclear; dsimplp;
        dtinjectionp; repeat dsplitp; dclear; dtgenp;
        dswap; dclear;
        dtsubstep_l;
        by dpmembernilp.
    }
    (* periodic *)
    difp.
    {
      repeat dclear; dsimpl.
      dif; dsplitp; dclear.
      dif; dsplitp; dclear.
      dswap; dtinjectionp; repeat dsplitp.
      dclear; dswap; dclear; dtgenp.
      by dtsubstep_l; dpmembernilp.
    }
    dtmergeentailsifp.

    (* By lemma 89 and lemma 99 on (1), (2), and (3) *)
    dxchg 0 2; dswap; dtsubstposp.
    dswap; dtsubstposp.
    eapply DSCut; first (by repeat dclear; apply DTL83_1 with
      (A := {-A (on n', event[]-> CPLSend ' n ' m) /\ (Fs' ' n').1 = c' -}));
      dtsubstp_r.

  (* Thus, from (5) and (6), we need to show that *)
  dtsubstneg; dtsubstneg.

  (* That is *)
  eapply DSCut; first (by repeat dclear; apply DTL83_1 with
    (A := {-A (on n', event[]-> CPLSend ' n ' m) /\ (Fs' ' n').1 = c' -}));
    dtsubst_l; dclear.

  (* By lemma 105, there are two cases that are similar *)
  match goal with
  | |- Context _ _ ||- _, {-A (eventuallyp ?H1_) /\ (eventuallyp ?H2_) =>> _ -} =>
    eapply DSCut; first by (repeat dclear; apply DTL102_2 with
      (A1 := H1_) (A2 := H2_))
  end; dttrans; dclear.
  dtorentailsp_c; difp; last by [].
  dsplit.

  {
    (* From assumption A_1, we need to prove *)
    dhave {-A
      (on n', event[]-> CPLSend ' n ' m) /\ (Fs' ' n').1 = c =>>
      (alwaysp^ ~on n', event[]-> CPLSend ' n ' m) /\ (Fs' ' n').1 = c
    -}.
    {
      eapply DSCut; first (by repeat dclear; apply DTAndHA_R with
        (A' := {-A (Fs' ' n').1 = c -})
        (H := {-A on n', event[]-> CPLSend ' n ' m -})
        (A := {-A alwaysp^ ~on n', event[]-> CPLSend ' n ' m -})).
      dsplitp; dswap; dclear.
      dsplitp; dclear.
      by difp.
    }
    dtsubstneg.

    (* By lemma 106, we need to prove *)
    eapply DSCut; first (by repeat dclear; apply DTAndComm with
      (A1 := {-A alwaysp^ ~on n', event[]-> CPLSend ' n ' m -})
      (A2 := {-A (Fs' ' n').1 = c -})); dtsubst_r; dclear.
    eapply DSCut; first (by repeat dclear; apply DTAndAssoc with
      (A1 := {-A (Fs' ' n').1 = c -})
      (A2 := {-A alwaysp^ ~on n', event[]-> CPLSend ' n ' m -})
      (A3 := {-A eventuallyp ((on n', event[]-> CPLSend ' n ' m) /\ (Fs' ' n').1 = c') -}));
      dtsubst_r; dclear.
    eapply DSCut; first (by repeat dclear; apply DTAndComm with
      (A1 := {-A alwaysp^ ~on n', event[]-> CPLSend ' n ' m -})
      (A2 := {-A eventuallyp ((on n', event[]-> CPLSend ' n ' m) /\ (Fs' ' n').1 = c') -}));
      dtsubst_r; dclear.
    eapply DSCut; first (by repeat dclear; apply DTL103_2 with
      (A1 := {-A on n', event[]-> CPLSend ' n ' m -})
      (A2 := {-A (Fs' ' n').1 = c' -}));
      dtsubstneg.

    eapply DSCut; first (by repeat dclear; apply DTAndComm with
      (A1 := {-A on n', event[]-> CPLSend ' n ' m -})
      (A2 := {-A (Fs' ' n').1 = c' -}));
      dtsubst_r; dclear.
    eapply DSCut; first (by repeat dclear; apply DTAndAssoc with
      (A1 := {-A (Fs' ' n').1 = c -})
      (A2 := {-A (Fs' ' n').1 = c' -})
      (A3 := {-A on n', event[]-> CPLSend ' n ' m -}));
      dtsubst_l; dclear.
    eapply DSCut; first (by repeat dclear; apply DTAndComm with
      (A1 := {-A ((Fs' ' n').1 = c /\ (Fs' ' n').1 = c') -})
      (A2 := {-A on n', event[]-> CPLSend ' n ' m -}));
      dtsubst_r; dclear.

    eapply DSCut; first (by repeat dclear; apply DTAndComm with
      (A1 := {-A (Fs' ' n').1 = c -})
      (A2 := {-A (Fs' ' n').1 = c' -})); dtsubst_r.

    duse DPEqual3; dforallp {-t (Fs' ' n').1 -}; dforallp c'; dforallp c;
      dtgenp; dtsubst_r; dclear.
    eapply DSCut; first (by repeat dclear; apply DTEntailsAndDropLeft with
      (A1 := {-A on n', event[]-> CPLSend ' n ' m -})
      (A2 := {-A c' = c -})); dtsubstneg.
    eapply DSCut; first (by repeat dclear; apply DTEventuallyPAlways with
      (A := {-A c' = c -}); [| repeat constructor]); dtsubstneg.
    eapply DSCut; first (by repeat dclear; apply DTL80 with
      (A := {-A c' = c -})); dtsubstneg.
    duse DPEqualSymm; dforallp c'; dforallp c; dtgenp; dclean; dtsubst_l; repeat dautoeq.
    by exact: DTEntailsTautology.
  }

  {
    (* From assumption A_1, we need to prove *)
    dhave {-A
      (on n', event[]-> CPLSend ' n ' m) /\ (Fs' ' n').1 = c' =>>
      (alwaysp^ ~on n', event[]-> CPLSend ' n ' m) /\ (Fs' ' n').1 = c'
    -}.
    {
      eapply DSCut; first (by repeat dclear; apply DTAndHA_R with
        (A' := {-A (Fs' ' n').1 = c' -})
        (H := {-A on n', event[]-> CPLSend ' n ' m -})
        (A := {-A alwaysp^ ~on n', event[]-> CPLSend ' n ' m -})).
      dsplitp; dswap; dclear.
      dsplitp; dclear.
      by difp.
    }
    dtsubstneg.

    (* By lemma 106, we need to prove *)
    eapply DSCut; first (by repeat dclear; apply DTAndComm with
      (A1 := {-A alwaysp^ ~on n', event[]-> CPLSend ' n ' m -})
      (A2 := {-A (Fs' ' n').1 = c' -})); dtsubst_r; dclear.
    eapply DSCut; first (by repeat dclear; apply DTAndAssoc with
      (A1 := {-A (Fs' ' n').1 = c' -})
      (A2 := {-A alwaysp^ ~on n', event[]-> CPLSend ' n ' m -})
      (A3 := {-A eventuallyp ((on n', event[]-> CPLSend ' n ' m) /\ (Fs' ' n').1 = c) -}));
      dtsubst_r; dclear.
    eapply DSCut; first (by repeat dclear; apply DTAndComm with
      (A1 := {-A alwaysp^ ~on n', event[]-> CPLSend ' n ' m -})
      (A2 := {-A eventuallyp ((on n', event[]-> CPLSend ' n ' m) /\ (Fs' ' n').1 = c) -}));
      dtsubst_r; dclear.
    eapply DSCut; first (by repeat dclear; apply DTL103_2 with
      (A1 := {-A on n', event[]-> CPLSend ' n ' m -})
      (A2 := {-A (Fs' ' n').1 = c -}));
      dtsubstneg.

    eapply DSCut; first (by repeat dclear; apply DTAndComm with
      (A1 := {-A on n', event[]-> CPLSend ' n ' m -})
      (A2 := {-A (Fs' ' n').1 = c -}));
      dtsubst_r; dclear.
    eapply DSCut; first (by repeat dclear; apply DTAndAssoc with
      (A1 := {-A (Fs' ' n').1 = c' -})
      (A2 := {-A (Fs' ' n').1 = c -})
      (A3 := {-A on n', event[]-> CPLSend ' n ' m -}));
      dtsubst_l; dclear.
    eapply DSCut; first (by repeat dclear; apply DTAndComm with
      (A1 := {-A ((Fs' ' n').1 = c' /\ (Fs' ' n').1 = c) -})
      (A2 := {-A on n', event[]-> CPLSend ' n ' m -}));
      dtsubst_r; dclear.

    duse DPEqual3; dforallp {-t (Fs' ' n').1 -}; dforallp c'; dforallp c;
      dtgenp; dtsubst_r; dclear.
    eapply DSCut; first (by repeat dclear; apply DTEntailsAndDropLeft with
      (A1 := {-A on n', event[]-> CPLSend ' n ' m -})
      (A2 := {-A c' = c -})); dtsubstneg.
    eapply DSCut; first (by repeat dclear; apply DTEventuallyPAlways with
      (A := {-A c' = c -}); [| repeat constructor]); dtsubstneg.
    eapply DSCut; first (by repeat dclear; apply DTL80 with
      (A := {-A c' = c -})); dtsubstneg.
    duse DPEqualSymm; dforallp c'; dforallp c; dtgenp; dclean; dtsubst_l; repeat dautoeq.
    by exact: DTEntailsTautology.
  }
Qed.

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
  dforall n; dforall n'; dforall m; dforall c; dif.

  (* By InvSe *)
  set A := {-A
    (n', c) \in (Fs ' n).2 /\
    (eventuallyp on n, event[0]<- CSLDeliver ' n' ' (c, m)) ->
    Fn = n -> CPLDeliver ' n' ' m \notin Fois -}.
  eapply DSCut; first (by repeat dclear; apply DPInvSe with (A := A);
    [by dautoclosed]).

  (* request *)
  difp.
  {
    (* This proof is simpler to write without the self operator *)
    match goal with
    | |- Context _ _ ||- _, {-A self ?A_ -} =>
      eapply DSCut; first (by repeat dclear; apply DPSInv_2 with (A := A_))
    end; difp; last by [].
    rewrite /restrict_assertion /=; dclean.
    dptoprequestselfelimif_l; dtsubst_r; dclear.

    dforall e.
    duse DPIR; dforallp e; dsimplp.
    dcase {-t ? e -}; dexistsp e_m; dexistsp e_n'; dtgenp;
      dtsubstep_l; dswap; dtsubste_l; dclear; dautoeq.
    dcase {-t ? Fs ' ? Fn -}; dexistsp s_r; dexistsp s_c; dtgenp;
      dtsubstep_l; dswap; dclear; dsimplp.
    dtinjectionp; dtsubstneg.

    repeat (rewrite /AEntails; dtmergeif; dtsubst_r; dclear).
    repeat (dtandassoc_l; dtsubst_r; dclear).
    dtifsubste'; dsplitp; dclear; difp; last by [].
    by dpmembernil; dtgenp; exact: DTEntailsAlwaysC.
  }

  (* indication *)
  difp.
  {
    (* This proof is simpler to write without the self operator *)
    match goal with
    | |- Context _ _ ||- _, {-A self ?A_ -} =>
      eapply DSCut; first (by repeat dclear; apply DPSInv_2 with (A := A_))
    end; difp; last by [].
    rewrite /restrict_assertion /=; dclean.
    dforall i; dforall e.
    dpsubindicationselfelimif_l; dtsubst_r; dclear.

    dhave {-A
      on n, event[i]<- e =>>
      (Fs' ' n, Fors, Fois) = (indication perfect_link) ' n ' (Fs ' n) ' (i, e)
    -}.
    {
      dclear.
      duse DPII; dforallp i; dforallp e.
      dtsubstneg.
      rewrite /AOn /AEntails; match goal with
      | |- context[ {-A ?H1_ /\ ?H2_ -> ?A_ -} ] =>
        eapply DSCut; first (by repeat dclear; apply DTMergeIf with
          (H1 := H1_) (H2 := H2_) (A := A_))
      end; dtsubst_l; dclear.
      dtifsubste'; dsplitp; dclear; difp; last by [].
      by dtgen; dif; dif.
    }
    repeat (rewrite /AEntails; dtmergeif; dtsubst_r; dclear).
    match goal with
    | |- Context _ _ ||- _, {-A ?H1_ /\ ?H2_ =>> ?A_ -} =>
      eapply DSCut; first (by repeat dclear; apply DTAndComm with
        (A1 := H1_) (A2 := H2_))
    end; dtsubst_r; dclear.
    rewrite /AOn; match goal with
    | |- Context _ _ ||- _, {-A ?H1_ /\ (?H2_ /\ ?H3_) =>> ?A_ -} =>
      eapply DSCut; first (by repeat dclear; apply DTAndAssoc with
        (A1 := H1_) (A2 := H2_) (A3 := H3_))
    end; dtsubst_l; dclear.

    dsimplp.
    dcase {-t (? i, ? e) -}; dexistsp m'; dexistsp c'; dexistsp n'';
      dtinjectionp; dsplitp; dtgenp;
      dtsubste_l; dautoeq; dxchg 1 2;
      dtsubstep_l; dautoeq; dswap; dclear; dswap; dtgenp;
      dtsubste_l; dautoeq;
      dtsubstep_l; dautoeq; dswap; dclear.
    dcase {-t ? Fs ' ? n -}; dexistsp s_r; dexistsp s_c; dtgenp;
      dtsubstep_l; dswap;
      dtsubste_l; dclear;
      dsimplp.
    dcase {-t FCount ' (? n'', ? c') ' ? s_r == 0 -}; dorp; dtgenp;
      dtsubstep_l; dsimplp;
      dtinjectionp; last first.
    {
      dtsubstneg.
      repeat (rewrite /AEntails; dtmergeif; dtsubst_r; dclear).
      repeat (dtandassoc_l; dtsubst_r; dclear).
      dtifsubste'; dsplitp; dclear; difp; last by [].
      by dpmembernil; dtgenp; exact: DTEntailsAlwaysC.
    }

    dhave {-A
      (n'', c') \notin s_r
    -}.
    {
      dswap.
      duse DPMemberReflect; dforallp {-t (n'', c') -}; dforallp s_r.
      dswap; dtsubstep_l; dsimplp; dsplitp; dclear.
      dhave {-A
        TFalse = TTrue <=> AFalse
      -}.
      {
        dtgen; dsplit; dif.
        - by eapply DSCut; first (by repeat dclear; apply DPNotEqual with
          (x1 := TFalse) (x2 := TTrue)); dnotp.
        - by dexfalso.
      }
      dtsubstp_l.

      dnot; dswap; dnotp.
      dsplit; last by [].
      by dnot; dnotp.
    }
    dxchg 0 2; dclear.

    match goal with
    | |- Context _ ({-A ?H_ =>> ?A_ -} :: _) ||- _, _ =>
      dhave {-A H_ =>> H_ /\ A_ -}
    end.
    {
      dsplitp; dswap; dclear.
      dtgen; dif; dswap; difp; first by [].
      by dsplit; dassumption.
    }
    dswap; dclear.
    dtsubstneg.
    repeat (rewrite /AEntails; dtmergeif; dtsubst_r; dclear).
    repeat (dtandassoc_l; dtsubst_r; dclear).
    dtifsubste'; dsplitp; dclear; difp; last by [].

    eapply DSCut; first (by repeat dclear; apply DSEM with
      (A := {-A n'' = n' /\ m' = m -})); dorp.

    (* true *)
    {
      dsplitp.
      dtgenp; dtsubste_l; dxchg 1 2; dtsubstep_l; dautoeq; dswap; dclear; dswap.
      dtgenp; dtsubste_l; dautoeq; dclear.
      dsimpl.
      dhave {-A
        (on n, event[0]<- CSLDeliver ' n' ' (c', m)) /\
        Fs' ' n = (s_c, s_r :|: [(n', c')]) /\
        Fors = [] /\
        Fois = [CPLDeliver ' n' ' m] /\
        (n', c) \in s_r /\
        eventuallyp (on n, event[0]<- CSLDeliver ' n' ' (c, m)) =>>
        (n', c) \in s_r /\
        (on n, event[0]<- CSLDeliver ' n' ' (c', m)) /\
        eventuallyp (on n, event[0]<- CSLDeliver ' n' ' (c, m))
      -}.
      {
        do 3 (match goal with
        | |- Context _ _ ||- _, {-A ?H1_ /\ ?H2_ /\ ?H3_ =>> _ -} =>
          eapply DSCut; first (by repeat dclear; apply DTEntailsAndDropLeft with
            (A1 := H2_) (A2 := H3_))
        end; dtsubstneg).

        match goal with
        | |- Context _ _ ||- _, {-A ?H1_ /\ ?H2_ /\ ?H3_ =>> _ -} =>
          eapply DSCut; first (by repeat dclear; apply DTAndAssoc with
            (A1 := H1_) (A2 := H2_) (A3 := H3_)); dtsubst_l; dclear;
          eapply DSCut; first (by repeat dclear; apply DTAndComm with
            (A1 := H1_) (A2 := H2_)); dtsubst_r; dclear;
          eapply DSCut; first (by repeat dclear; apply DTAndAssoc with
            (A1 := H2_) (A2 := H1_) (A3 := H3_)); dtsubst_r; dclear
        end.

        by exact: DTEntailsTautology.
      }
      dtsubstneg.

      duse L44; dforallp n; dforallp n'; dforallp m; dforallp c'; dforallp c;
        difp; first by dassumption.
      match goal with
      | |- Context _ ({-A self ?A_ -} :: _) ||- _, _ =>
        eapply DSCut; first (by repeat dclear; apply DPSInv_1 with (A := A_))
      end; difp; first by dhead.
      rewrite /restrict_assertion /=; dclean.
      dtmergeif; dtsubstp_l.
      match goal with
      | |- context[ {-A self-event /\ ?A1_ /\ ?A2_ -} ] =>
        eapply DSCut; first (by repeat dclear; apply DTAndAssoc with
          (A1 := {-A self-event -}) (A2 := A1_) (A3 := A2_))
      end; dtsubstp_r.
      rewrite /AOn; match goal with
      | |- context[ {-A self-event /\ (?A1_ /\ ?A2_) -} ] =>
        eapply DSCut; first (by repeat dclear; apply DTAndAssoc with
          (A1 := {-A self-event -}) (A2 := A1_) (A3 := A2_)); dtsubstp_r;
        eapply DSCut; first (by repeat dclear; apply DTAndComm with
          (A1 := {-A self-event -}) (A2 := A1_)); dtsubstp_l;
        eapply DSCut; first (by repeat dclear; apply DTAndAssoc with
          (A1 := A1_) (A2 := {-A self-event -}) (A3 := A2_)); dtsubstp_l;
        eapply DSCut; first (by repeat dclear; apply DTAndComm with
          (A1 := {-A self-event -}) (A2 := A2_)); dtsubstp_l
      end.
      duse DPSubIndicationSelfElim; dforallp {-t 0 -}; dforallp {-t CSLDeliver ' n' ' (c', m) -};
        dtgenp; dclean; dtsubstp_l.
      dtsubstneg; dclear.

      eapply DSCut; first (by repeat dclear; apply DTAndComm with
        (A1 := {-A (n', c) \in s_r -}) (A2 := {-A c' = c -})); dtsubst_r; dclear.
      dtgen; dif; dsplitp.
      dxchg 1 2; dtgenp; dtsubstep_l; dautoeq; dswap; dclear.
      by dnotp.
    }

    (* false *)
    {
      dhave {-A
        always (CPLDeliver ' n' ' m \notin [CPLDeliver ' n'' ' m'])
      -}.
      {
        dtgen; dnot.
        duse DPMemberCons;
          dforallp {-t CPLDeliver ' n' ' m -};
          dforallp {-t CPLDeliver ' n'' ' m' -};
          dforallp {-t [] -}.
        dsplitp; dswap; dclear; difp; first by [].
        dswap; dclear; dorp; last by dpmembernilp.
        dtinjectionp; dswap; dnotp.

        duse DPEqualSymm; dforallp n'; dforallp n''; dtgenp; dclean;
          dtsubstp_l; repeat dautoeq.
        duse DPEqualSymm; dforallp m; dforallp m'; dtgenp; dclean;
          dtsubstp_l; repeat dautoeq.
        by [].
      }
      by exact: DTEntailsAlwaysC.
    }
  }

  (* periodic *)
  difp.
  {
    (* This proof is simpler to write without the self operator *)
    match goal with
    | |- Context _ _ ||- _, {-A self ?A_ -} =>
      eapply DSCut; first (by repeat dclear; apply DPSInv_2 with (A := A_))
    end; difp; last by [].
    rewrite /restrict_assertion /=; dclean.
    dptopperiodicselfelimif_l; dtsubst_r; dclear.

    duse DPPe; dsimplp.
    dtinjectionp; dtsubstneg.

    repeat (rewrite /AEntails; dtmergeif; dtsubst_r; dclear).
    repeat (dtandassoc_l; dtsubst_r; dclear).
    dtifsubste'; dsplitp; dclear; difp; last by [].
    by dpmembernil; dtgenp; exact: DTEntailsAlwaysC.
  }

  by dclean.
Qed.

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
      (S := {-A forall: (* s *) (n', c) \in ($$0).2 -});
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
    (S := {-A forall: (* s *) (n', $$1) \in ($$0).2 /\
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
