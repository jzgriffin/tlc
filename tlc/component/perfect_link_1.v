(* TLC in Coq
 *
 * Module: tlc.component.perfect_link_1
 * Purpose: Contains the local specification of the perfect link PL_1 property.
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

Lemma L37_1 Delta : Context Delta [::] ||- perfect_link, {-A
  forall: forall: forall: forall: forall: (* n, n', c, m, m' *)
  $$4 \in UCorrect /\ $$3 \in UCorrect ->
  self-event /\ (on $$4, (0, CSLSend ' $$3 ' ($$2, $$1)) \in Fors) =>>
  always^ ~(self-event /\ on $$4, (0, CSLSend ' $$3 ' ($$2, $$0)) \in Fors)
-}.
Proof.
  dforall n; dforall n'; dforall c; dforall m; dforall m'; dif; dsplitp.

  (* By InvL *)
  dhave {-A
    self-event /\ (on n, (0, CSLSend ' n' ' (c, m)) \in Fors) =>>
    (Fs' ' n).1 = c
  -}.
  {
    repeat dclear.
    eapply DSCut; first by apply DPInvL with (A := {-A
      on n, (0, CSLSend ' n' ' (c, m)) \in Fors ->
      (Fs' ' n).1 = c -});
      [dautoclosed | repeat constructor].

    (* request *)
    difp.
      dforall e; dif; dsplitp; dswap; dsimplp; dsimpl; simpl.
      dcase {-t ? e -}; dexistsp e_m; dexistsp e_n'; dtgenp;
        dtsubstep_l; dswap; dclear; dsimplp.
      dcase {-t ? Fs ' ? Fn -}; dexistsp s_r; dexistsp s_c; dtgenp;
        dtsubstep_l; dswap; dclear; dsimplp.
      dtinjectionp; repeat dsplitp.

      dif; dsplitp.
      dtgenp; dxchg 1 2; dtsubstep_l; dswap; dclear.
      dtgenp; dtsubste_l; dclear; dsimpl.
      dswap; dtgenp; dtsubstep_l; dswap; dclear.

      duse DPMemberCons;
        dforallp {-t (0, CSLSend ' n' ' (c, m)) -};
        dforallp {-t (0, CSLSend ' e_n' ' (CSucc ' s_c, e_m)) -};
        dforallp {-t [] -};
        dsplitp; dswap; dclear; difp; first by [].
      dorp; last by duse DPMemberNil;
        dforallp {-t (0, CSLSend ' n' ' (c, m)) -}; dnotp.
      dtinjectionp; dsplitp; dclear.
      dsplitp; dclear; dsplitp; dtgenp; dtsubste_l; dautoeq.
      by repeat dclear; exact: DPEqual.

    (* indication *)
    difp.
      dforall i; dforall e; dif; dsplitp; dswap; dsimplp; dsimpl; simpl.
      dcase {-t (? i, ? e) -}; dexistsp e_m; dexistsp e_c; dexistsp e_n; dtgenp;
        dtsubstep_l; dswap; dclear; dsimplp.
      dcase {-t ? Fs ' ? Fn -}; dexistsp s_r; dexistsp s_c; dtgenp;
        dtsubstep_l; dswap; dclear; dsimplp.
      dcase {-t FCount ' (? e_n, ? e_c) ' ? s_r == 0 -}; dorp;
        dtgenp; dtsubstep_l; dswap; dclear; dsimplp;
        dtinjectionp; repeat dsplitp;
        dclear; dtgenp; dif; dsplitp; dclear; dswap; dtsubstep_l; dswap; dclear;
        by duse DPMemberNil; dforallp {-t (0, CSLSend ' n' ' (c, m)) -}; dnotp.

    (* periodic *)
    difp.
      dif; dsplitp; dswap; dsimplp; dsimpl; simpl.
      dtinjectionp; repeat dsplitp;
      dclear; dtgenp; dif; dsplitp; dclear; dswap; dtsubstep_l; dswap; dclear;
      by duse DPMemberNil; dforallp {-t (0, CSLSend ' n' ' (c, m)) -}; dnotp.

    by dtmergeentailsifp.
  }

  (* By InvS *)
  dhave {-A
    self-event /\ (Fs ' n).1 >= c =>>
    (self-event =>> (Fs ' n).1 >= c)
  -}.
  {
    repeat dclear.
    eapply DSCut; first by apply DPInvS with
      (S0 := {-A forall: (* s *) ($$0).1 >= c -});
      [| dautoclosed | repeat constructor].
    dforallp n.

    (* request *)
    difp.
      dforall s; dforall e; dsimpl; dif.
      dcase {-t ? s -}; dexistsp s_r; dexistsp s_c;
        dtgenp; dtsubste_l; dtsubstep_l; dswap; dclear;
        dautoeq; dsimpl; dsimplp.
      dcase {-t ? e -}; dexistsp e_n'; dexistsp e_m;
        dtgenp; dtsubste_l; dclear; dautoeq; dsimpl.
      by duse DPSuccGreaterEqual; dforallp s_c; dforallp c; difp.

    (* indication *)
    difp.
      dforall s; dforall i; dforall e; dsimpl; dif.
      dcase {-t ? s -}; dexistsp s_r; dexistsp s_c;
        dtgenp; dtsubste_l; dtsubstep_l; dswap; dclear;
        dautoeq; dsimpl; dsimplp.
      dcase {-t (? i, ? e) -}; dexistsp e_m; dexistsp e_c; dexistsp e_n;
        dtgenp; dtsubste_l; dclear; dautoeq; dsimpl.
      by dcase {-t FCount ' (? e_n, ? e_c) ' ? s_r == 0 -}; dorp;
        dtgenp; dtsubste_l; dclear; dsimpl.

    (* periodic *)
    difp.
      by dforall s; dsimpl; dif.

    by dsimplp.
  }

  (* By ASA on (1) and (2) *)
  dhave {-A
    on n, self-event /\ ((0, CSLSend ' n' ' (c, m)) \in Fors) =>>
    always^ (self-event -> (Fs ' n).1 >= c)
  -}.
  {
    eapply DSCut; first (by repeat dclear; apply DPASA with
      (S := {-A forall: (* s *) ($$0).1 >= c -})
      (A := {-A on n, (0, CSLSend ' n' ' (c, m)) \in Fors -})
      (A' := {-A (Fs ' n).1 >= c -});
      [| dautoclosed | dautoclosed | dautoclosed
        | repeat constructor | repeat constructor]).
    dforallp n; dsimplp.

    (* post *)
    difp.
      duse DPEqualGreaterEqual; dforallp {-t (Fs' ' n).1 -}; dforallp c.
      by dtgenp; dclean; dxchg 1 2; dtsubstposp.

    (* pre *)
    difp.
      by dassumption.

    eapply DSCut; first (by repeat dclear; apply DSAndAssoc with
      (A1 := {-A self-event -})
      (A2 := {-A Fn = n -})
      (A3 := {-A (0, CSLSend ' n' ' (c, m)) \in Fors -}));
      dtgenp; dclean; dtsubstp_r.
    eapply DSCut; first (by repeat dclear; apply DSAndComm with
      (A1 := {-A self-event -})
      (A2 := {-A Fn = n -}));
      dtgenp; dclean; dtsubstp_l.
    eapply DSCut; first (by repeat dclear; apply DSAndAssoc with
      (A1 := {-A Fn = n -})
      (A2 := {-A self-event -})
      (A3 := {-A (0, CSLSend ' n' ' (c, m)) \in Fors -}));
      dtgenp; dclean; dtsubstp_l.
    by [].
  }

  (* By InvL *)
  dhave {-A
    self-event /\ (Fs ' n).1 >= c =>>
    ~(on n, (0, CSLSend ' n' ' (c, m')) \in Fors)
  -}.
  {
    repeat dclear.
    eapply DSCut; first by apply DPInvL with (A := {-A
      (Fs ' n).1 >= c ->
      ~(on n, (0, CSLSend ' n' ' (c, m')) \in Fors)
    -}); [dautoclosed | repeat constructor].

    (* request *)
    difp.
      dforall e; dif; dsplitp; dswap; dsimplp.
      dcase {-t ? e -}; dexistsp e_m; dexistsp e_n'; dtgenp;
        dtsubstep_l; dswap; dclear; dsimplp.
      dcase {-t ? Fs ' ? Fn -}; dexistsp s_r; dexistsp s_c; dtgenp;
        dtsubstep_l; dsimplp.
      dtinjectionp; repeat dsplitp.

      dswap; dtgenp; dtsubste_l; dclear.
      dif; dnot.
      dsplitp; dtgenp.
      dxchg 1 3; dtsubstep_l; dswap.
      dxchg 1 5; dtsubstep_l; dswap; dclear.
      dtsubstep_l; dswap; dclear; dsimplp.

      duse DPMemberCons;
        dforallp {-t (0, CSLSend ' n' ' (c, m')) -};
        dforallp {-t (0, CSLSend ' e_n' ' (CSucc ' s_c, e_m)) -};
        dforallp {-t [] -};
        dsplitp; dswap; dclear; difp; first by dassumption.
      dorp; last by duse DPMemberNil;
        dforallp {-t (0, CSLSend ' n' ' (c, m')) -}; dnotp.
      dtinjectionp; dsplitp; dclear.
      dsplitp; dclear; dsplitp; dswap; dclear; dtgenp;
        dtsubstep_l; dautoeq; dswap; dclear.

      duse DPGreaterEqual; dforallp s_c; dforallp {-t s_c.+1 -}.
      dsplitp; dswap; dclear; difp; first (by []); dswap; dclear; dorp.
      - (* equal *)
        eapply DSCut; first by eapply DSubInjection with
          (t1 := {-t s_c -}) (t2 := {-t s_c.+1 -}); [by [] | auto_mem].
        by dnotp.
      - (* not equal *)
        duse DPNotLessThanIfGreaterThan; dforallp s_c; dforallp {-t s_c.+1 -}.
        difp; last by dnotp.
        by duse DPLessThanSucc; dforallp s_c.

    (* indication *)
    difp.
      dforall i; dforall e; dif; dsplitp; dswap; dsimplp.
      dcase {-t (? i, ? e) -}; dexistsp e_m; dexistsp e_c; dexistsp e_n;
        dtgenp; dtsubstep_l; dswap; dclear; dsimplp.
      dcase {-t ? Fs ' ? Fn -}; dexistsp s_r; dexistsp s_c; dtgenp;
        dtsubstep_l; dsimplp.
      by dcase {-t FCount ' (? e_n, ? e_c) ' ? s_r == 0 -}; dorp;
        dtgenp; dtsubstep_l; dswap; dclear; dsimplp;
        dtinjectionp; repeat dsplitp;
        dif; dclear; dnot; dsplitp; dclear;
        dswap; dxchg 0 2; dtgenp; dtsubstep_l; dswap; dclear;
        duse DPMemberNil; dforallp {-t (0, CSLSend ' n' ' (c, m')) -}; dnotp.

    (* periodic *)
    difp.
      dif; dsplitp; dclear; dsimplp.
      by dtinjectionp; repeat dsplitp;
        dif; dclear; dnot; dsplitp; dclear;
        dswap; dxchg 0 2; dtgenp; dtsubstep_l; dswap; dclear;
        duse DPMemberNil; dforallp {-t (0, CSLSend ' n' ' (c, m')) -}; dnotp.

    by dtmergeentailsifp.
  }

  (* From (3) and (4) *)
  dhave {-A
    (self-event -> (Fs ' n).1 >= c) ->
    (self-event -> (self-event /\ (Fs ' n).1 >= c))
  -}; first by repeat dif; dsplit; [| dswap; difp].
  dtgenp; dclean.
  dxchg 1 2; dtsubstposp.
  dswap; dtsubstposp.
  dhave {-A
    (self-event -> ~ on n, (0, CSLSend ' n' ' (c, m')) \in Fors) ->
    ~ (self-event /\ on n, (0, CSLSend ' n' ' (c, m')) \in Fors)
  -}; first by dif; dnot; dsplitp; dxchg 1 2; dswap; difp; [| dnotp; dassumption].
  dtgenp; dclean.
  dtsubstposp.

  eapply DSCut; first (by repeat dclear; apply DSAndAssoc with
    (A1 := {-A Fn = n -})
    (A2 := {-A self-event -})
    (A3 := {-A (0, CSLSend ' n' ' (c, m)) \in Fors -}));
    dtgenp; dclean; dtsubstp_r.
  eapply DSCut; first (by repeat dclear; apply DSAndComm with
    (A1 := {-A Fn = n -})
    (A2 := {-A self-event -}));
    dtgenp; dclean; dtsubstp_l.
  eapply DSCut; first (by repeat dclear; apply DSAndAssoc with
    (A1 := {-A self-event -})
    (A2 := {-A Fn = n -})
    (A3 := {-A (0, CSLSend ' n' ' (c, m)) \in Fors -}));
    dtgenp; dclean; dtsubstp_l.
  by [].
Qed.

Lemma L37_2 Delta : Context Delta [::] ||- perfect_link, {-A
  forall: forall: forall: forall: forall: (* n, n', c, m, m' *)
  $$4 \in UCorrect /\ $$3 \in UCorrect ->
  self-event /\ (on $$4, (0, CSLSend ' $$3 ' ($$2, $$1)) \in Fors) =>>
  alwaysp^ ~(self-event /\ on $$4, (0, CSLSend ' $$3 ' ($$2, $$0)) \in Fors)
-}.
Proof.
  dforall n; dforall n'; dforall c; dforall m; dforall m'; dif.

  (* By L37_1 *)
  duse L37_1; dforallp n; dforallp n'; dforallp c; dforallp m; dforallp m';
    difp; first by [].

  eapply DSCut; first (by repeat dclear; apply DTL105_1 with
    (H := {-A self-event /\ on n, (0, CSLSend ' n' ' (c, m)) \in Fors -})
    (A := {-A self-event /\ on n, (0, CSLSend ' n' ' (c, m')) \in Fors -})).
  by dtsubstposp.
Qed.

Lemma L39 Delta : Context Delta [::] ||- perfect_link, {-A
  forall: forall: forall: forall: (* n, n', m, c *)
  $$3 \in UCorrect /\ $$2 \in UCorrect ->
  on $$2, event[0]<- CSLDeliver ' $$3 ' ($$0, $$1) /\
    ($$3, $$0) \notin (Fs ' $$2).2 ~>
  on $$2, event[]<- CPLDeliver ' $$3 ' $$1
 -}.
Proof.
  dforall n; dforall n'; dforall m; dforall c.
  dif; dsplitp.

  duse DPOI; dforallp n'; dforallp {-t CPLDeliver ' n ' m -}; dsimplp.
  eapply DSCut; first (by repeat dclear; apply DTL121 with
    (A := {-A on n', event[]<- CPLDeliver ' n ' m -}));
    dtsubstposp.

  dhave {-A
    on n', event[0]<- CSLDeliver ' n ' (c, m) /\ (n, c) \notin (Fs ' n').2 ->
    on n', self-event /\ CPLDeliver ' n ' m \in Fois
  -}.
  {
    repeat dclear.
    dif; dsplitp; dswap; dsplitp.
    dsplit; first by dassumption.
    dsplit; first by dleft; dexists {-t 0 -};
      dsplit; dsplitp; [| dclear; dsplitp].
    duse DPII; dforallp {-t 0 -}; dforallp {-t CSLDeliver ' n ' (c, m) -};
      dsimplp; dsplitp; dswap; dclear; difp; first by dassumption.
    dswap; dxchg 0 3; dtgenp; dtsubstep_l; dswap; dclear.
    dcase {-t ? Fs ' ? n' -}; dexistsp s_r; dexistsp s_c;
      dtgenp; dtsubstep_l; dsimplp.
    dswap; dxchg 1 2; dtsubstep_l; dswap; dclear; dswap.
    dcase {-t FCount ' (? n, ? c) ' ? s_r == 0 -}; dorp;
      dtgenp; dtsubstep_l; dsimplp.
    - dswap; dclear; dtinjectionp; repeat dsplitp.
      dxchg 0 2; dtgenp; dtsubste_l.
      by duse DPMemberSingleton; dforallp {-t CPLDeliver ' n ' m -}.
    - dclear; dswap; dsimplp.
      duse DPMemberReflect; dforallp {-t (n, c) -}; dforallp s_r.
      dxchg 1 2; dswap; dtsubstep_l; dsimplp; dswap; dclear;
        dsplitp; dswap; dclear; difp; first by repeat dclear; exact: DPEqual.
      by dswap; dnotp.
  }
  dtgenp; dclean.

  by rewrite /AFollowedBy; dswap; dttransp.
Qed.

Lemma L41 Delta : Context Delta [::] ||- perfect_link, {-A
  forall: forall: forall: (* n, n', c *)
  $$2 \in UCorrect /\ $$1 \in UCorrect ->
  self-event /\ ($$2, $$0) \in (Fs ' $$1).2 =>>
  exists: (* m *)
    eventuallyp (on $$2, event[0]<- CSLDeliver ' $$3 ' ($$1, $$0) /\
      CPLDeliver ' $$3 ' $$0 \in Fois)
 -}.
Proof.
  dforall n; dforall n'; dforall c; dif; dsplitp.

  (* Instantiate InvSA *)
  eapply DSCut; first (by repeat dclear; apply DPInvSA with
    (S0 := {-A forall: (* s *) (n, c) \in ($$0).2 -})
    (A := {-A exists: (* m *)
      (on n', event[0]<- CSLDeliver ' n ' (c, $$0) /\
        CPLDeliver ' n ' $$0 \in Fois) -});
    [| dautoclosed | dautoclosed | repeat constructor | repeat constructor]);
  dforallp n'.

  (* initialize *)
  difp.
    repeat dsimpl.
    by duse DPMemberNil; dforallp {-t (n, c) -}.

  (* request *)
  difp.
    dforall e; dif; dsplitp; dswap; dsplitp; dswap; dsplitp; dsimplp.
    dcase {-t ? Fs ' ? Fn -}; dexistsp s_r; dexistsp s_c; dtgenp; dtsubstep_l;
      dsimplp.
    dcase {-t ? e -}; dexistsp e_m; dexistsp e_n; dtgenp; dtsubstep_l;
      dautoeq; dsimplp.
    dtinjectionp; repeat dsplitp.

    dxchg 1 5; dtgenp; dtsubstep_l.
    dxchg 1 4; dswap; dtsubstep_l; dautoeq.
    repeat dsimplp; dsplitp.
    by dnotp.

  (* indication *)
  difp.
    dforall i; dforall e; dif; dsplitp; dswap; dsplitp; dswap; dsplitp; dsimplp.
    dcase {-t ? Fs ' ? Fn -}; dexistsp s_r; dexistsp s_c; dtgenp; dtsubstep_l;
      dsimplp.
    dcase {-t (? i, ? e) -}; dexistsp e_m; dexistsp e_c; dexistsp e_n;
      dtinjectionp; dsplitp;
      dtgenp; dxchg 1 2; dtsubstep_l;
        dswap; dxchg 1 5; dtsubstep_l;
        dswap; dclear; dswap; dautoeq;
      dtgenp; dtsubstep_l;
        dswap; dxchg 1 4; dtsubstep_l;
        dswap; dclear; dautoeq;
      dsimplp.
    dcase {-t FCount ' (? e_n, ? e_c) ' ? s_r == 0 -}; dorp;
      dtgenp; dtsubstep_l; dswap; dclear; dsimplp;
      dtinjectionp; repeat dsplitp;
      dxchg 1 4; dtgenp; dtsubstep_l; dswap; dclear;
      dxchg 1 2; dswap; dtsubstep_l; dswap; dclear;
      repeat dsimplp; dsplitp;
      try by dnotp.
    dexists e_m; dswap.
    duse DPMemberSetUnion;
      dforallp s_r; dforallp {-t [(e_n, e_c)] -}; dforallp {-t (n, c ) -};
      dsplitp; dclear; difp; [by [] |]; dswap; dclear; dorp;
      first by dswap; dnotp.
    duse DPMemberCons;
      dforallp {-t (n, c ) -}; dforallp {-t (e_n, e_c) -}; dforallp {-t [] -};
      dsplitp; dswap; dclear; difp; [by [] |]; dswap; dclear; dorp;
      last by duse DPMemberNil; dforallp {-t (n, c) -}; dnotp.
    dswap; dclear; dxchg 0 2; dclear.
    dsplit; first by dassumption.
    dtgenp; dtsubste_l; dclear.
    dtinjectionp; dsplitp; repeat (dtgenp; dtsubste_l; dautoeq; dclear).
    dsplit; [by [] | dclear].
    by duse DPMemberSingleton; dforallp {-t CPLDeliver ' e_n ' e_m -}.

  (* periodic *)
  difp.
    dsimpl; repeat dclear; dif; repeat (dsplitp; dswap).
    dxchg 0 2; dtinjectionp; repeat dsplitp.
    do 2 (dswap; dclear); dtgenp; dxchg 1 2; dtsubstep_l; dswap; dclear.
    by dswap; dnotp.

  dsimplp.
  rewrite /AOn; dexistsandclosed_l; dtgenp; dclean; dtsubstp_l.
  rewrite /AOn; dtandelimselfap.
  rewrite /AOn; dexistsandclosed_r; dtgenp; dclean; dtsubstp_r.
  dteventuallyp'p.

  set A := {-A on n', event[0]<- CSLDeliver ' n ' (c, $$0) /\
    CPLDeliver ' n ' $$0 \in Fois -}.
  dhave {-A
    (eventuallyp exists: A) <=> (exists: eventuallyp A)
  -}; first by apply DTL127_3.
  by dtsubstp_l.
Qed.

Lemma L40 Delta : Context Delta [::] ||- perfect_link, {-A
  forall: forall: forall: (* n, n', c *)
  $$2 \in UCorrect /\ $$1 \in UCorrect ->
  self-event /\ (on $$1, ($$2, $$0) \in (Fs ' $$1).2) =>>
  exists: (* m *)
    eventuallyp (on $$3, (0, CSLSend ' $$2 ' ($$1, $$0)) \in Fors /\
      self-event /\
      eventually on $$2, event[]<- CPLDeliver ' $$3 ' $$0)
 -}.
Proof.
  dforall n; dforall n'; dforall c; dif.

  (* By Lemma 41 *)
  duse L41; dforallp n; dforallp n'; dforallp c; difp; first by [].

  (* By SL_2 *)
  duse PL_SL_2; dforallp n'; dforallp n.

  (* By OR' *)
  dhave {-A
    forall: (* m *)
    on n, event[0]-> CSLSend ' n' ' (c, $$0) =>>
    eventuallyp (self-event /\ on n, (0, CSLSend ' n' ' (c, $$0)) \in Fors)
  -}.
  {
    dforall m.
    duse DPOR'; dforallp n; dforallp {-t 0 -}; dforallp {-t CSLSend ' n' ' (c, m) -}.
    by eapply DSCut; first (by repeat dclear; apply DTL123 with
      (A := {-A self-event /\ on n, (0, CSLSend ' n' ' (c, m)) \in Fors -}));
      dtsubstposp.
  }

  (* By Lemma 85 on (2) and (3) *)
  dhave {-A
    forall: (* m *)
    on n', event[0]<- CSLDeliver ' n ' (c, $$0) =>>
    eventuallyp (self-event /\ on n, (0, CSLSend ' n' ' (c, $$0)) \in Fors)
  -}.
  {
    dforall m; dswap; dforallp {-t (c, m) -}.
    eapply DTL85; first by dhead.
    by dswap; dforallp m.
  }
  do 2 (dswap; dclear).

  (* By OI *)
  dhave {-A
    forall: (* m *)
    on n', self-event /\ CPLDeliver ' n ' $$0 \in Fois =>>
    eventually (on n', event[]<- CPLDeliver ' n ' $$0)
  -}.
  {
    dforall m.
    duse DPOI; dforallp n'; dforallp {-t CPLDeliver ' n ' m -}.
    by eapply DSCut; first (by repeat dclear; apply DTL121 with
      (A := {-A on n', event[]<- CPLDeliver ' n ' m -}));
      dtsubstposp.
  }

  (* By (1), (4), and (5) *)
  dhave {-A
    self-event /\ (n, c) \in (Fs ' n').2 =>>
    exists: (* m *)
      eventuallyp (eventuallyp (self-event /\
        (on n, (0, CSLSend ' n' ' (c, $$0)) \in Fors)) /\
        eventually on n', event []<- CPLDeliver ' n ' $$0)
  -}.
  {
    dswap; dxchg 1 2; dswap.
    eapply DSCut; first (by repeat dclear; apply DSAndElimSelf with
      (A := {-A Fn = n' -}));
      dtgenp; dclean; dtsubstp_r.
    eapply DSCut; first (by repeat dclear; apply DTAndAssoc with
      (A1 := {-A Fn = n' -})
      (A2 := {-A Fn = n' -})
      (A3 := {-A event[0]<- CSLDeliver ' n ' (c, $$0) /\
        CPLDeliver ' n ' $$0 \in Fois -}));
      dtsubstp_l.
    eapply DSCut; first (by apply DSAndComm with
      (A1 := {-A Fn = n' -})
      (A2 := {-A event[0]<- CSLDeliver ' n ' (c, $$0) /\
        CPLDeliver ' n ' $$0 \in Fois -}));
      dtgenp; dclean; dtsubstp_l.
    eapply DSCut; first (by repeat dclear; apply DTAndAssoc with
      (A1 := {-A event[0]<- CSLDeliver ' n ' (c, $$0) -})
      (A2 := {-A CPLDeliver ' n ' $$0 \in Fois -})
      (A3 := {-A Fn = n' -}));
      dtsubstp_l.
    eapply DSCut; first (by apply DSAndComm with
      (A1 := {-A CPLDeliver ' n ' $$0 \in Fois -})
      (A2 := {-A Fn = n' -}));
      dtgenp; dclean; dtsubstp_l.
    eapply DSCut; first (by repeat dclear; apply DTAndAssoc with
      (A1 := {-A Fn = n' -})
      (A2 := {-A event[0]<- CSLDeliver ' n ' (c, $$0) -})
      (A3 := {-A on n', CPLDeliver ' n ' $$0 \in Fois -}));
      dtsubstp_r.
    eapply DSCut; first (by repeat dclear; apply DSAndElimSelf with
      (A := {-A event[0]<- CSLDeliver ' n ' (c, $$0) -}));
      dtgenp; dclean; dtsubstp_r.
    eapply DSCut; first (by repeat dclear; apply DTAndAssoc with
      (A1 := {-A Fn = n' -})
      (A2 := {-A event[0]<- CSLDeliver ' n ' (c, $$0) -})
      (A3 := {-A event[0]<- CSLDeliver ' n ' (c, $$0) -}));
      dtsubstp_r.
    eapply DSCut; first (by repeat dclear; apply DTAndAssoc with
      (A1 := {-A on n', event[0]<- CSLDeliver ' n ' (c, $$0) -})
      (A2 := {-A event[0]<- CSLDeliver ' n ' (c, $$0) -})
      (A3 := {-A on n', CPLDeliver ' n ' $$0 \in Fois -}));
      dtsubstp_l.
    eapply DSCut; first (by repeat dclear; apply DTAndAssoc with
      (A1 := {-A event[0]<- CSLDeliver ' n ' (c, $$0) -})
      (A2 := {-A Fn = n' -})
      (A3 := {-A CPLDeliver ' n ' $$0 \in Fois -}));
      dtsubstp_r.
    eapply DSCut; first (by apply DSAndComm with
      (A1 := {-A event[0]<- CSLDeliver ' n ' (c, $$0) -})
      (A2 := {-A Fn = n' -}));
      dtgenp; dclean; dtsubstp_l.
    eapply DSCut; first (by repeat dclear; apply DTAndAssoc with
      (A1 := {-A Fn = n' -})
      (A2 := {-A event[0]<- CSLDeliver ' n ' (c, $$0) -})
      (A3 := {-A CPLDeliver ' n ' $$0 \in Fois -}));
      dtsubstp_l.
    dswap; dtsubstposp.
    duse DPSubIndicationSelf; dtsubstposp.
    by dswap; dtsubstposp.
  }
  do 3 (dswap; dclear).

  eapply DSCut; first (by repeat dclear; apply DTL126 with
    (A1 := {-A self-event /\ on n, (0, CSLSend ' n' ' (c, $$0)) \in Fors -})
    (A2 := {-A on n', event[]<- CPLDeliver ' n ' $$0 -}));
    dtsubstposp.
  eapply DSCut; first (by apply DSAndComm with
    (A1 := {-A self-event -})
    (A2 := {-A on n, (0, CSLSend ' n' ' (c, $$0)) \in Fors -}));
    dtgenp; dclean; dtsubstp_l.
  eapply DSCut; first (by repeat dclear; apply DTAndAssoc with
    (A1 := {-A on n, (0, CSLSend ' n' ' (c, $$0)) \in Fors -})
    (A2 := {-A self-event -})
    (A3 := {-A eventually (on n', event[]<- CPLDeliver ' n ' $$0) -}));
    dtsubstp_l.
  eapply DSCut; first (by repeat dclear; apply DTAndAssoc with
    (A1 := {-A Fn = n -})
    (A2 := {-A (0, CSLSend ' n' ' (c, $$0)) \in Fors -})
    (A3 := {-A self-event /\ eventually (on n', event[]<- CPLDeliver ' n ' $$0) -}));
    dtsubstp_l.

  dhave {-A on n', (n, c) \in (Fs ' n').2 =>> (n, c) \in (Fs ' n').2 -};
    first by dtgen; dif; dsplitp; dassumption.
  by dtsubstnegp.
Qed.

Lemma L38 Delta : Context Delta [::] ||- perfect_link, {-A
  forall: forall: forall: forall: (* n, n', m, c *)
  $$3 \in UCorrect /\ $$2 \in UCorrect ->
  on $$2, event[0]<- CSLDeliver ' $$3 ' ($$0, $$1) =>>
  eventually (on $$2, event[]<- CPLDeliver ' $$3 ' $$1) \/
  exists: (* m' *)
    eventuallyp (on $$4, (0, CSLSend ' $$3 ' ($$1, $$0)) \in Fors /\ self-event /\
      eventually on $$3, event[]<- CPLDeliver ' $$4 ' $$0)
 -}.
Proof.
  dforall n; dforall n'; dforall m; dforall c; dif.

  dhave {-A (n, c) \notin (Fs ' n').2 \/ (n, c) \in (Fs ' n').2 -}.
  {
    duse DPMemberReflect; dforallp {-t (n, c) -}; dforallp {-t (Fs ' n').2 -};
      dtgenp; dclean; dtsubst_l; dclear.
    dcase {-t FCount ' (? n, ? c) ' (? Fs ' ? n').2 == 0 -}; dorp;
      dtgenp; dtsubste_l; dclear; dsimpl; repeat dclear;
      by dif.
  }

  eapply DSCut; first (by eapply DTEntailsAlwaysC with
    (H := {-A on n', event[0]<- CSLDeliver ' n ' (c, m) -});
    dtgenp; dhead); dswap; dclear.
  eapply DSCut; first (by apply DTEntailsTautology with
    (A := {-A on n', event[0]<- CSLDeliver ' n ' (c, m) -}));
    rewrite -DTEntailsAndSplitP.
  eapply DSCut; first (by apply DSOrDistribAnd2 with
    (A := {-A on n', event[0]<- CSLDeliver ' n ' (c, m) -})
    (A1 := {-A (n, c) \notin (Fs ' n').2 -})
    (A2 := {-A (n, c) \in (Fs ' n').2 -}));
    dtgenp; dclean; dtsubstp_l.

  (* Align false case with L39 precondition *)
  dhave {-A
    (on n', event[0]<- CSLDeliver ' n ' (c, m)) /\ (n, c) \notin (Fs ' n').2 =>>
    on n', event[0]<- CSLDeliver ' n ' (c, m) /\ (n, c) \notin (Fs ' n').2
  -}.
  {
    repeat dclear; dtgen; dif; repeat dsplitp.
    by dsplit; [| dsplit]; dassumption.
  }
  dtsubstposp.

  (* Align true case with L40 precondition *)
  dhave {-A
    (on n', event[0]<- CSLDeliver ' n ' (c, m)) /\ (n, c) \in (Fs ' n').2 =>>
    self-event /\ (on n', (n, c) \in (Fs ' n').2)
  -}.
  {
    repeat dclear; dtgen; dif; repeat dsplitp.
    dsplit; last by dsplit; dassumption.
    by dswap; duse DPSubIndicationSelf; dtsubstposp.
  }
  dtsubstposp.

  (* By Lemma 39 *)
  duse L39; dforallp n; dforallp n'; dforallp m; dforallp c; difp; first by dassumption.
  dtsubstposp.

  (* By Lemma 40 *)
  duse L40; dforallp n; dforallp n'; dforallp c; difp; first by dassumption.
  dtsubstposp.

  by [].
Qed.

(* Reliable delivery
 * If a correct node n sends a message m to a correct node n', then n' will
 * eventually deliver m.
 *)
Theorem PL_1 Delta : Context Delta [::] ||- perfect_link, {-A
  forall: forall: forall: (* n, n', m *)
  $$2 \in UCorrect /\ $$1 \in UCorrect ->
  on $$2, event[]-> CPLSend ' $$1 ' $$0 ~>
  on $$1, event[]<- CPLDeliver ' $$2 ' $$0
 -}.
Proof.
  dforall n; dforall n'; dforall m; dif; dsplitp.

  (* By IR *)
  dhave {-A
    exists: (* c *)
    on n, event[]-> CPLSend ' n' ' m =>>
    self-event /\ on n, (0, CSLSend ' n' ' ($$0, m)) \in Fors
  -}.
  {
    duse DPIR; dforallp {-t CPLSend ' n' ' m -}; dsimplp.
    dcase {-t ? Fs ' ? Fn -}; dexistsp r; dexistsp c; dtgenp;
      dtsubstep_l; dswap; dclear; dsimplp; dtinjectionp.
    dexists {-t c.+1 -}; dtgen; dsplitp; dswap; dclear.
    dif; dsplitp; dxchg 0 2; difp; first by dassumption.
    repeat dsplitp.
    dsplit; first by dxchg 0 3; duse DPTopRequestSelf; dtsubstposp.
    dsplit; first by dassumption.
    dclear; dtgenp; dtsubste_l; dclear.
    by duse DPMemberSingleton; dforallp {-t (0, CSLSend ' n' ' (c.+1, m)) -}.
  }
  dexistsp c.

  (* By OR *)
  dhave {-A
    (self-event /\ on n, ((0, CSLSend ' n' ' (c, m)) \in Fors)) =>>
    eventually (on n, event[0]-> CSLSend ' n' ' (c, m))
  -}.
  {
    repeat dclear.

    duse DPOR; dforallp n; dforallp {-t 0 -}; dforallp {-t CSLSend ' n' ' (c, m) -}.
    eapply DSCut; first (by apply DTEventually' with
      (A := {-A on n, event[0]-> CSLSend ' n' ' (c, m) -}));
      dtsubstposp.
    eapply DSCut; first (by repeat dclear; apply DTAndAssoc with
      (A1 := {-A Fn = n -})
      (A2 := {-A self-event -})
      (A3 := {-A (0, CSLSend ' n' ' (c, m)) \in Fors -}));
      dtsubstp_r.
    eapply DSCut; first (by repeat dclear; apply DSAndComm with
      (A1 := {-A Fn = n -})
      (A2 := {-A self-event -}));
      dtgenp; dclean; dtsubstp_l.
    eapply DSCut; first (by repeat dclear; apply DTAndAssoc with
      (A1 := {-A self-event -})
      (A2 := {-A Fn = n -})
      (A3 := {-A (0, CSLSend ' n' ' (c, m)) \in Fors -}));
      dtsubstp_l.

    by [].
  }
  dtsubstposp_keep; dswap; dclear; dswap; rewrite -DTEntailsAndSplitP.
  eapply DSCut; first (by repeat dclear; apply DTAndAssoc with
    (A1 := {-A self-event -})
    (A2 := {-A on n, (0, CSLSend ' n' ' (c, m)) \in Fors -})
    (A3 := {-A eventually on n, event[0]-> CSLSend ' n' ' (c, m) -}));
    dtsubstp_l.

  (* By SL_1 and Axiom 1 *)
  dhave {-A
    on n, event[0]-> CSLSend ' n' ' (c, m) ~>
    on n', event[0]<- CSLDeliver ' n ' (c, m)
  -}.
  {
    duse PL_SL_1; dforallp n; dforallp n'; dforallp {-t (c, m) -};
      difp; first by dsplit; dassumption.
    by rewrite DTEntailsAndSplitP.
  }

  (* By Lemma 86 on (1) and (2) *)
  (* It is quicker to rewrite (2) into (1) and use Lemma 120 *)
  dtsubstposp; eapply DSCut; first (by apply DTL120_1 with
    (A := {-A on n', event[0]<- CSLDeliver ' n ' (c, m) -}));
    dtsubstp_r.

  (* By Lemma 96 on (3) and Lemma 38 *)
  dhave {-A
    on n, event[]-> CPLSend ' n' ' m =>>
    self-event /\ (on n, (0, CSLSend ' n' ' (c, m)) \in Fors) /\
    eventually (eventually (on n', event[]<- CPLDeliver ' n ' m) \/
      exists: (* m *) eventuallyp ((self-event /\
        on n, (0, CSLSend ' n' ' (c, $$0)) \in Fors) /\
        eventually on n', event[]<- CPLDeliver ' n ' $$0))
  -}.
  {
    duse L38; dforallp n; dforallp n'; dforallp m; dforallp c; difp;
      first by dsplit; dassumption.
    (* It is quicker to rewrite L38 into (3) *)
    dtsubstposp.
    eapply DSCut; first (by repeat dclear; apply DTAndAssoc with
      (A1 := {-A Fn = n -})
      (A2 := {-A (0, CSLSend ' n' ' (c, $$0)) \in Fors -})
      (A3 := {-A self-event /\ eventually (on n', event[]<- CPLDeliver ' n ' $$0) -}));
      dtsubstp_r.
    eapply DSCut; first (by repeat dclear; apply DTAndAssoc with
      (A1 := {-A on n, (0, CSLSend ' n' ' (c, $$0)) \in Fors -})
      (A2 := {-A self-event -})
      (A3 := {-A eventually (on n', event[]<- CPLDeliver ' n ' $$0) -}));
      dtsubstp_r.
    eapply DSCut; first (by repeat dclear; apply DSAndComm with
      (A1 := {-A on n, (0, CSLSend ' n' ' (c, $$0)) \in Fors -})
      (A2 := {-A self-event -}));
      dtgenp; dtsubstp_l.
    by [].
  }
  dswap; dclear.

  (* That is *)
  dteventuallyorcomm; dtsubstp_l.
  dteventuallyexistscomm; dtsubstp_l.
  dteventuallyidemp; dtsubstp_r.
  match goal with
  | |- context[ {-A eventually eventuallyp ?A_ -} ] =>
    eapply DSCut; first (by repeat dclear; apply DTL109_3 with (A := A_))
  end; dtsubstposp.

  (* By Lemma 37 *)
  dhave {-A
    on n, event[]-> CPLSend ' n' ' m =>>
    self-event /\ (on n, (0, CSLSend ' n' ' (c, m)) \in Fors) /\
    (eventually (on n', event[]<- CPLDeliver ' n ' m) \/
      exists: (* m *) (self-event /\
        (on n, (0, CSLSend ' n' ' (c, $$0)) \in Fors) /\
        eventually on n', event[]<- CPLDeliver ' n ' $$0))
  -}.
  {
    match goal with
    | |- context[ {-A self-event /\ ?A2_ /\ ?A3_ -} ] =>
      eapply DSCut; first (by repeat dclear; apply DTAndAssoc with
        (A1 := {-A self-event -}) (A2 := A2_) (A3 := A3_))
    end; dtsubstp_r.

    eapply DSCut; first (by repeat dclear; apply DTAndElimSelf with
      (A := {-A self-event /\ on n, (0, CSLSend ' n' ' (c, m)) \in Fors -}));
      dtsubstp_r.
    match goal with
    | |- context[ {-A (?A1_ /\ ?A1_) /\ ?A3_ -} ] =>
      eapply DSCut; first (by repeat dclear; apply DTAndAssoc with
        (A1 := A1_) (A2 := A1_) (A3 := A3_))
    end; repeat dautoeq; dtsubstp_l.
    dtordistrib2_2.

    dtandintoexists; dtsubstposp.
    match goal with
    | |- context[ {-A exists: ?A1_ /\ (?A2_ \/ ?A3_) -} ] =>
      set A1 := A1_; set A2 := A2_; set A3 := A3_
    end.

    dhave {-A
      A1 /\ (A2 \/ A3) <=>
      A1 /\ A2 \/ A1 /\ A3
    -}; first (by repeat dclear; apply DTOrDistrib2); dtsubstp_l.
    eapply DSCut; first (by repeat dclear; eapply DTAndComm with
      (A1 := A1) (A2 := A2)); dtsubstp_l.
    eapply DSCut; first (by repeat dclear; eapply DTAndComm with
      (A1 := A1) (A2 := A3)); dtsubstp_l.

    (* Future case *)
    set A1' := {-A always^ ~(self-event /\ on n, (0, CSLSend ' n' ' (c, $$0)) \in Fors) -}.
    rewrite -/A1 -/A2 -/A3.
    dhave {-A
      forall:
      (A2 /\ A1) =>>
      (A2 /\ A1')
    -}; first (by dforall m'; dtandha_l; dsplitp; dswap; dclear; dsplitp; dclear; difp;
      first by duse L37_1; dforallp n; dforallp n'; dforallp c; dforallp m; dforallp m'; difp;
      first by dsplit; dassumption); dtsubstposp.
    eapply DSCut; first (by repeat dclear; apply DTL103_1 with
      (A1 := {-A self-event /\ on n, (0, CSLSend ' n' ' (c, $$0)) \in Fors -})
      (A2 := {-A eventually on n', event[]<- CPLDeliver ' n ' $$0 -}));
      dtsubstposp.
    clear A1'.

    (* Past case *)
    set A1' := {-A alwaysp^ ~(self-event /\ on n, (0, CSLSend ' n' ' (c, $$0)) \in Fors) -}.
    rewrite -/A1 -/A2 -/A3.
    dhave {-A
      forall:
      (A3 /\ A1) =>>
      (A3 /\ A1')
    -}; first (by dforall m'; dtandha_l; dsplitp; dswap; dclear; dsplitp; dclear; difp;
      first by duse L37_2; dforallp n; dforallp n'; dforallp c; dforallp m; dforallp m'; difp;
      first by dsplit; dassumption); dtsubstposp.
    eapply DSCut; first (by repeat dclear; apply DTL103_2 with
      (A1 := {-A self-event /\ on n, (0, CSLSend ' n' ' (c, $$0)) \in Fors -})
      (A2 := {-A eventually on n', event[]<- CPLDeliver ' n ' $$0 -}));
      dtsubstposp.
    clear A1'.

    clear A1 A2 A3.
    set A1 := {-A self-event /\ (on n, (0, CSLSend ' n' ' (c, $$0)) \in Fors) -}.
    set A2 := {-A eventually on n', event[]<- CPLDeliver ' n ' $$0 -}.
    eapply DSCut; first (by repeat dclear; apply DTOrDistrib2 with
      (A1 := A1) (A2 := A2) (A3 := A2)); dtsubstp_r.
    eapply DSCut; first (by repeat dclear; apply DTOrElimSelf with
      (A := A2)); dtsubstp_l.

    by repeat (match goal with
    | |- context[ {-A (self-event /\ ?A2_) /\ ?A3_ -} ] =>
      eapply DSCut; first (by repeat dclear; apply DTAndAssoc with
        (A1 := {-A self-event -}) (A2 := A2_) (A3 := A3_))
    end; dtsubstp_l).
  }

  (* Thus *)
  eapply DSCut; first (repeat dclear; by apply DTOrComm with
    (H1 := {-A eventually on n', event[]<- CPLDeliver ' n ' m -})
    (H2 := {-A exists: (* m *) self-event /\
      (on n, (0, CSLSend ' n' ' (c, $$0)) \in Fors) /\
      eventually on n', event[]<- CPLDeliver ' n ' $$0 -}));
    dtsubstp_l.
  eapply DSCut; first (repeat dclear; by apply DTAndAssoc with
    (A1 := {-A self-event -})
    (A2 := {-A on n, (0, CSLSend ' n' ' (c, m)) \in Fors -})
    (A3 := {-A (exists: (* m *) self-event /\
      (on n, (0, CSLSend ' n' ' (c, $$0)) \in Fors) /\
      eventually on n', event[]<- CPLDeliver ' n ' $$0) \/
      eventually on n', event[]<- CPLDeliver ' n ' m -}));
    dtsubstp_r.
  eapply DSCut; first (repeat dclear; by apply DTAndAssoc with
    (A1 := {-A self-event -})
    (A2 := {-A on n, (0, CSLSend ' n' ' (c, $$0)) \in Fors -})
    (A3 := {-A eventually on n', event[]<- CPLDeliver ' n ' $$0 -}));
    dtsubstp_r.
  eapply DSCut; first (repeat dclear; by apply DTOrDistrib2 with
    (A1 := {-A self-event /\ on n, (0, CSLSend ' n' ' (c, m)) \in Fors -})
    (A2 := {-A exists: (* m *) (self-event /\
      (on n, (0, CSLSend ' n' ' (c, $$0)) \in Fors)) /\
      eventually on n', event[]<- CPLDeliver ' n ' $$0 -})
    (A3 := {-A eventually on n', event[]<- CPLDeliver ' n ' m -}));
    dtsubstp_l.
  eapply DSCut; first (by repeat dclear; eapply DTAndExampleExists with
    (H1 := {-A self-event /\ on n, (0, CSLSend ' n' ' (c, $$0)) \in Fors -})
    (H2 := {-A eventually on n', event[]<- CPLDeliver ' n ' $$0 -})
    (x := {-t m -})); dsimplp; dtsubstposp.
  eapply DSCut; first (by repeat dclear; apply DTEntailsAndDropLeft with
    (A1 := {-A self-event /\ on n, (0, CSLSend ' n' ' (c, m)) \in Fors -})
    (A2 := {-A eventually on n', event[]<- CPLDeliver ' n ' m -}));
    dtsubstposp.
  by eapply DSCut; first (by repeat dclear; apply DTOrElimSelf with
    (A := {-A eventually on n', event[]<- CPLDeliver ' n ' m -}));
    dtsubstp_l.
Qed.
