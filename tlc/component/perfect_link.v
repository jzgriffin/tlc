(* TLC in Coq
 *
 * Module: tlc.component.perfect_link
 * Purpose: Contains the functional implementation and logical specification
 * of the perfect link component.
 *)

Require Import mathcomp.ssreflect.eqtype.
Require Import mathcomp.ssreflect.seq.
Require Import mathcomp.ssreflect.ssrbool.
Require Import mathcomp.ssreflect.ssreflect.
Require Import mathcomp.ssreflect.ssrnat.
Require Import tlc.component.component.
Require Import tlc.component.stubborn_link.
Require Import tlc.logic.all_logic.
Require Import tlc.operation.orientation.
Require Import tlc.semantics.all_semantics.
Require Import tlc.syntax.all_syntax.
Require Import tlc.utility.all_utility.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Functional implementation *)
Definition perfect_link :=
  let slc := 0 in
  let initialize :=
    {-t fun: (* n *)
      (0, [])
     -} in
  let request :=
    {-t fun: fun: fun: (* n, s, ir *)
      let: ($0, $1) := $$1 in: (* {c, r} *)
      match: $$1 with:
      { CPLSend ' $0 ' $1 (* {n', m} *) ->
        let: $0 := $(1, 0).+1 in: (* c' *)
        let: $0 := (term_of_nat slc, CSLSend ' $(1, 0) ' ($$0, $(1, 1))) in: (* or *)
        (($$1, $(3, 1)), [$$0], [])
       }
    -} in
  let indication :=
    {-t fun: fun: fun: (* n', s, ii *)
      let: ($0, $1) := $$1 in: (* {c, r} *)
      match: $$1 with:
      { (pattern_of_nat slc, CSLDeliver ' $0 ' ($1, $2)) (* {n, c', m} *) ->
        if: ($0, $1) \in $(1, 1)
        then:
          ($$4, [], [])
        else:
          let: $0 := $(2, 1) :|: [($(1, 0), $(1, 1))] in: (* r' *)
          let: $0 := CPLDeliver ' $(2, 0) ' $(2, 2) in: (* oi *)
          (($(4, 0), $$1), [], [$$0])
       }
    -} in
  let periodic :=
    {-t fun: fun: (* n, s *)
      ($$0, [], [])
    -} in
  Component
    (Logic.eq_refl : term_computable initialize)
    (Logic.eq_refl : term_computable request)
    (Logic.eq_refl : term_computable indication)
    (Logic.eq_refl : term_computable periodic).

(* Specification *)

(* Lowered stubborn link properties *)
Lemma PL_SL_1 Delta : Context Delta [::] ||- perfect_link, {-A
  forall: forall: forall: (* n, n', m *)
  $$2 \in UCorrect /\ $$1 \in UCorrect ->
  on $$2, event[0]-> CSLSend ' $$1 ' $$0 =>>
  always eventually on $$1, event[0]<- CSLDeliver ' $$2 ' $$0
-}.
Proof.
  duse (DPLower (SL_1 Delta) perfect_link 0 (SL_1_TA Delta));
    rewrite /lower_assertion /=; dclean.

  dforall n; dforall n'; dforall m;
  dforallp n; dforallp n'; dforallp m.
  dif; dswap; difp; [by [] | dswap; dsplitp; dswap; dxchg 0 2].

  eapply DSCut; first (by repeat dclear; apply DTL124 with
    (Ap := {-A Fd <<< [0] -})
    (Ac := {-A eventually on n', event[0]<- CSLDeliver ' n ' m -}));
    dtsubstposp.
  eapply DSCut; first (by repeat dclear; apply DTL124 with
    (Ap := {-A Fd <<< [0] -})
    (Ac := {-A
      on n, event[0]-> CSLSend ' n' ' m ->
      Fd <<< [0] ~> on n', event[0]<- CSLDeliver ' n ' m -}));
    dtsubstposp.
  dtmergeentailsifp.

  dhave {-A
    (Fd <<< [0] /\ on n, event[0]-> CSLSend ' n' ' m) <->
    on n, event[0]-> CSLSend ' n' ' m
  -}.
  {
    dsplit; dif; first by dsplitp; dassumption.
    dsplit; last by [].
    by dsplitp; dclear; dsplitp; dtgenp; dtsubste_l;
      repeat dclear; eapply DPExtension.
  }
  dtgenp; dclean; dtsubstp_l.

  eapply DSCut.
    eapply DTL132 with
      (A1 := {-A on n, event[0]-> CSLSend ' n' ' m -})
      (B1 := {-A Fd <<< [0] -})
      (A2 := {-A on n, event[0]-> CSLSend ' n' ' m -})
      (B2 := {-A Fd <<< [0] =>> eventually on n', event[0]<- CSLDeliver ' n ' m -}).
    difp; first by dsplit; first by
      dtgen; dif; dsplitp; dclear; dsplitp; dtgenp; dtsubste_l;
      repeat dclear; eapply DPExtension.
  eapply DSCut; first (by repeat dclear; eapply DSAndElimSelf with
    (A := {-A on n, event[0]-> CSLSend ' n' ' m -}));
    dtgenp; dclean; dtsubstp_l.
  by eapply DSCut; first (by repeat dclear; eapply DTAndEntails with
    (H := {-A Fd <<< [0] -})
    (A := {-A eventually on n', event[0]<- CSLDeliver ' n ' m -}));
    dtsubstposp.
Qed.

Lemma PL_SL_2 Delta : Context Delta [::] ||- perfect_link, {-A
  forall: forall: forall: (* n, n', m *)
  on $$2, event[0]<- CSLDeliver ' $$1 ' $$0 <~
  on $$1, event[0]-> CSLSend ' $$2 ' $$0
-}.
Proof.
  duse (DPLower (SL_2 Delta) perfect_link 0 (SL_2_TA Delta));
    rewrite /lower_assertion /=; dclean.

  dforall n; dforall n'; dforall m;
  dforallp n; dforallp n'; dforallp m.

  eapply DSCut; first (by repeat dclear; apply DTL124 with
    (Ap := {-A Fd <<< [0] -})
    (Ac := {-A on n, event[0]<- CSLDeliver ' n' ' m ->
      eventuallyp on n', event[0]-> CSLSend ' n ' m -}));
    dtsubstposp.
  dtmergeentailsifp.

  dhave {-A
    (Fd <<< [0] /\ on n, event[0]<- CSLDeliver ' n' ' m) <->
    on n, event[0]<- CSLDeliver ' n' ' m
  -}.
  {
    dsplit; dif; first by dsplitp; dassumption.
    dsplit; last by [].
    by dsplitp; dclear; dsplitp; dtgenp; dtsubste_l;
      repeat dclear; eapply DPExtension.
  }
  by dtgenp; dclean; dtsubstp_l.
Qed.

(* Lemmas used in proving PL_1 *)

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
  by difp.
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
  forall: forall: forall: (* 2:n, 1:n', 0:m *)
  correct #2 /\ correct #1 ->
  on #2, event[]-> CPLSend ' #1 ' #0 ~>
  on #1, event[]<- CPLDeliver ' #2 ' #0
 -}.
Proof.
  (* Introduce context *)
  set C := perfect_link; rewrite -/C /empty_context.
  d_forallc n Hf_n; d_forallc n' Hf_n';
    d_forallc m Hf_m;
    simpl_embed.
  d_ifc; d_splitp.

  (* By IR *)
  d_have {-A
    exists: (* c *)
    on n, event[]-> CPLSend ' n' ' m =>>
    self-event /\ on n, ((0, CSLSend ' n' ' (#0, m)) \in Fors)
   -}.
  {
(*
    d_forallc c Hf_c; simpl_embed.
    eapply DTGeneralization; first by repeat constructor.
    d_ifc.
    d_use DPIR; d_forallp {-t CPLSend ' n' ' m -}; d_evalp.
    d_splitp; d_swap; d_clear; d_ifp; first by d_splitp; d_clear.

    d_destructp (fun t => {-A (Fs' ' Fn, Fors, Fois) = t -});
      d_existsp r Hf_r; d_existsp c_ Hf_c_; simpl_embed;
      d_splitp; d_swap; d_substp; d_evalp.
    d_destructpairp; repeat d_splitp.

    d_swap; d_substc; d_splitc;
      first by d_rotate 4; d_splitp; d_clear; d_splitp; d_swap; d_splitp;
      d_right; d_left; d_splitc; d_assumption.
    d_splitc; first by d_rotate 4; d_splitp.
    
    d_swap; d_substc; d_splitc; first by d_rotate 4; d_splitp.
    eapply DAPIn; first by [].
    by rewrite mem_seq1.
*)
    admit.
  }

  d_existsp c Hf_c; simpl_embed.

  (* By OR *)
  d_have {-A
    (self-event /\ on n, ((0, CSLSend ' n' ' (c, m)) \in Fors)) =>>
    eventually (on n, event[0]-> CSLSend ' n' ' (c, m))
   -}.
  {
    d_use DPOR; d_forallp n; d_forallp 0; d_forallp {-t CSLSend ' n' ' (c, m) -};
      simpl_embed.
    eapply DARewriteIfP; first by apply DTL121 with
      (A := {-A on n, event[0]-> CSLSend ' n' ' (c, m) -}).
    simpl_embed.

    d_swap; d_clear.
    d_have {-A
      self-event /\ on n, ((0, CSLSend ' n' ' (c, m)) \in Fors) =>>
      on n, (self-event /\ (0, CSLSend ' n' ' (c, m)) \in Fors)
     -}.
    {
      eapply DTGeneralization; first by repeat constructor.
      d_ifc; d_splitc; first by d_splitp; d_swap; d_splitp.
      d_splitc; first by d_splitp.
      by do 2 (d_splitp; d_swap).
    }

    eapply DTL77; first by d_head.
    by d_assumption.
  }

  (* Apply DTL96 on above assumptions *)
  d_have {-A
    on n, event[]-> CPLSend ' n' ' m ~>
    on n, event[0]-> CSLSend ' n' ' (c, m)
   -}.
  {
    d_swap.
    set A := {-A self-event /\ on n, ((0, CSLSend ' n' ' (c, m)) \in Fors) -}.
    set B := {-A on n, event[0]-> CSLSend ' n' ' (c, m) -}.
    set D := {-A on n, event[]-> CPLSend ' n' ' m -}.

    eapply DTL77; first by d_head.
    by d_assumption.
  }

  (* By SL_1 and Axiom 1 *)
  d_have {-A
    on n, event[0]-> CSLSend ' n' ' (c, m) =>>
    eventually (on n', event[0]<- CSLDeliver ' n ' (c, m))
   -}.
  {
    d_use_empty PL_SL_1; d_forallp n; d_forallp n'; simpl_embed.
    d_ifp; first by d_splitc; d_assumption.
    d_forallp {-t (c, m) -}; simpl_embed.

    eapply DARewriteIfP; first by apply DT1 with
      (A := {-A eventually on n', event[0]<- CSLDeliver ' n ' (c, m) -}).
    by simpl_embed.
  }

  (* By Lemma 86 on (1) and (2) *)
  d_have {-A
    on n, event[]-> CPLSend ' n' ' m =>>
    eventually on n', event[0]<- CSLDeliver ' n ' (c, m)
   -}.
  {
    by eapply DTL86; first by d_swap; d_head.
  }

  d_have {-A
    on n, event[]-> CPLSend ' n' ' m =>>
    (self-event /\ on n, ((0, CSLSend ' n' ' (c, m)) \in Fors)) /\
    (eventually on n', event[0]<- CSLDeliver ' n ' (c, m)) -}.
  {
    eapply DARewriteIffCR with
      (Arc := {-A (on n, event[]-> CPLSend ' n' ' m) ->
        ((self-event /\ on n, ((0, CSLSend ' n' ' (c, m)) \in Fors)) /\
        (eventually on n', event[0]<- CSLDeliver ' n ' (c, m))) -})
      (Arp := {-A ((on n, event[]-> CPLSend ' n' ' m) ->
        (self-event /\ on n, ((0, CSLSend ' n' ' (c, m)) \in Fors))) /\
        ((on n, event[]-> CPLSend ' n' ' m) ->
          (eventually on n', event[0]<- CSLDeliver ' n ' (c, m))) -}).
    eapply DSIfAndSplit with
      (Ap := {-A on n, event[]-> CPLSend ' n' ' m -})
      (Acl := {-A self-event /\ on n, ((0, CSLSend ' n' ' (c, m)) \in Fors) -})
      (Acr := {-A eventually on n', event[0]<- CSLDeliver ' n ' (c, m) -}).
    simpl_embed.

    set A := {-A on n, event[]-> CPLSend ' n' ' m ->
      self-event /\ on n, ((0, CSLSend ' n' ' (c, m)) \in Fors) -}.
    set B := {-A on n, event[]-> CPLSend ' n' ' m ->
      eventually on n', event[0]<- CSLDeliver ' n ' (c, m) -}.
    eapply DARewriteCongruentCL with
      (Arp := {-A always (A /\ B) -})
      (Arc := {-A (always A) /\ (always B) -});
      first by eapply DTL128_1.
    simpl_embed.

    by d_splitc; d_assumption.
  }

  (* By Lemma 96 on (3) and Lemma 38 *)
  d_have {-A
    on n, event[]-> CPLSend ' n' ' m =>>
    (self-event /\ (on n, ((0, CSLSend ' n' ' (c, m)) \in Fors))) /\
    eventually ((eventually (on n', event[]<- CPLDeliver ' n ' m)) \/
      exists: (* m *) (eventuallyp ((self-event /\ on n, ((0, CSLSend ' n' ' (c, #0)) \in Fors)) /\
        (eventually on n', event[]<- CPLDeliver ' n ' #0))))
   -}.
  {
    eapply DARewriteEntailsP with
      (Arp := {-A on n', event[0]<- CSLDeliver ' n ' (c, m) -})
      (Arc := {-A (eventually on n', event[]<- CPLDeliver ' n ' m) \/ exists: (* m *)
        (eventuallyp ((on n, self-event /\ (0, CSLSend ' n' ' (c, #0)) \in Fors) /\
          (eventually on n', event[]<- CPLDeliver ' n ' #0))) -}).
    {
      do 5 d_clear.
      d_use_empty L38; d_forallp n; d_forallp n'; simpl_embed.
      d_ifp; first by d_splitc; d_assumption.
      by d_forallp m; d_forallp c; simpl_embed.
    }
    simpl_embed; rewrite andbF.

    d_have {-A
      ((on n, self-event /\ ((0, CSLSend ' n' ' (c, m)) \in Fors)) /\
        eventually on n', event[]<- CPLDeliver ' n ' m) ->
      ((self-event /\ on n, ((0, CSLSend ' n' ' (c, m)) \in Fors)) /\
        eventually on n', event[]<- CPLDeliver ' n ' m) -}.
    {
      d_ifc; repeat d_splitp; d_splitc;
        first by d_splitc; [| d_splitc]; d_assumption.
      d_assumption.
    }

    d_swap.
    eapply DARewriteIfInExistsP with
      (Arp := {-A (on n, self-event /\ ((0, CSLSend ' n' ' (c, #0)) \in Fors)) /\
        eventually on n', event[]<- CPLDeliver ' n ' #0 -})
      (Arc := {-A (self-event /\ on n, ((0, CSLSend ' n' ' (c, #0)) \in Fors)) /\
        eventually on n', event[]<- CPLDeliver ' n ' #0 -});
      first by d_existsc m; simpl_embed; d_head.
    by rewrite /rewrite_pos_in_exists /=; simpl_embed.
  }

  d_have {-A
    on n, event[]-> CPLSend ' n' ' m =>>
    (self-event /\ on n, ((0, CSLSend ' n' ' (c, m)) \in Fors)) /\
    ((eventually (eventually (on n', event[]<- CPLDeliver ' n ' m))) \/
      (eventually (exists: (* m *)
        eventuallyp ((self-event /\ on n, ((0, CSLSend ' n' ' (c, #0)) \in Fors)) /\
          eventually (on n', event[]<- CPLDeliver ' n ' #0)))))
   -}.
  {
    set A := {-A exists: (* m *)
      eventuallyp ((self-event /\ on n, ((0, CSLSend ' n' ' (c, #0)) \in Fors)) /\
        (eventually on n', event[]<- CPLDeliver ' n ' #0)) -}.
    set B := {-A eventually (on n', event[]<- CPLDeliver ' n ' m) -}.

    eapply DARewriteCongruentPL with
      (Arp := {-A eventually (B \/ A) -})
      (Arc := {-A (eventually B) \/ (eventually A) -});
      first by eapply DTL127_1.
    by simpl_embed.
  }

  d_have {-A
    on n, event[]-> CPLSend ' n' ' m =>>
    (self-event /\ on n, ((0, CSLSend ' n' ' (c, m)) \in Fors)) /\
    ((eventually (on n', event[]<- CPLDeliver ' n ' m)) \/
      (exists: (* m *)
        eventually (eventuallyp ((self-event /\ on n, ((0, CSLSend ' n' ' (c, #0)) \in Fors)) /\
          eventually (on n', event[]<- CPLDeliver ' n ' #0)))))
   -}.
  {
    set A1 := {-A self-event /\ on n, ((0, CSLSend ' n' ' (c, m)) \in Fors) -}.
    set A2 := {-A (self-event /\ on n, ((0, CSLSend ' n' ' (c, m)) \in Fors)) /\
      (eventually on n', event[]<- CPLDeliver ' n ' m) -}.
    set B1 := {-A eventually eventually (on n', event[]<- CPLDeliver ' n ' m) -}.
    set B2 := {-A eventually (on n', event[]<- CPLDeliver ' n ' m) -}.

    eapply DARewriteCongruentPR with
      (Arc := {-A eventually eventually on n', event[]<- CPLDeliver ' n ' m -})
      (Arp := {-A eventually on n', event[]<- CPLDeliver ' n ' m -});
      first by eapply DTL84 with (A := {-A on n', event[]<- CPLDeliver ' n ' m -}).
    simpl_embed.

    set A3 := {-A self-event /\ on n, ((0, CSLSend ' n' ' (c, m)) \in Fors) -}.
    set A4 := {-A (self-event /\ on n, ((0, CSLSend ' n' ' (c, #0)) \in Fors)) /\
      eventually on n', event[]<- CPLDeliver ' n ' #0 -}.
    set B3 := {-A eventually eventually (on n', event[]<- CPLDeliver ' n ' m) -}.
    set B4 := {-A eventually (on n', event[]<- CPLDeliver ' n ' m) -}.

    eapply DARewriteCongruentPL with
      (Arp := {-A eventually (exists: (* m *) eventuallyp A4) -})
      (Arc := {-A (exists: (* m *) (eventually eventuallyp A4)) -});
      first by eapply DTL127_2 with (A := {-A eventuallyp A4 -}).
    by simpl_embed.
  }

  d_have {-A
    on n, event[]-> CPLSend ' n' ' m =>>
    (self-event /\ on n, ((0, CSLSend ' n' ' (c, m)) \in Fors)) /\
    ((eventually (on n', event[]<- CPLDeliver ' n ' m)) \/
      (exists: (* m *)
        ((eventually^ ((self-event /\ on n, ((0, CSLSend ' n' ' (c, #0)) \in Fors)) /\
          eventually (on n', event[]<- CPLDeliver ' n ' #0))) \/
        ((self-event /\ on n, ((0, CSLSend ' n' ' (c, #0)) \in Fors)) /\
          eventually (on n', event[]<- CPLDeliver ' n ' #0)) \/
        (eventuallyp^ ((self-event /\ on n, ((0, CSLSend ' n' ' (c, #0)) \in Fors)) /\
          eventually (on n', event[]<- CPLDeliver ' n ' #0))))))
   -}.
  {
    set A1 := {-A self-event /\ on n, ((0, CSLSend ' n' ' (c, #0)) \in Fors) -}.
    set A2 := {-A ((self-event /\ on n, ((0, CSLSend ' n' ' (c, #0)) \in Fors)) /\
      (eventually on n', event[]<- CPLDeliver ' n ' #0)) -}.
    set B1 := {-A eventually (on n', event[]<- CPLDeliver ' n ' #0) -}.
    eapply DARewriteEntailsInExistsP with
      (Arp := {-A eventually eventuallyp A2 -})
      (Arc := {-A eventually^ A2 \/ A2 \/ eventuallyp^ A2 -});
      first by d_existsc m; simpl_embed; eapply DTL109_3_a.
    by rewrite /rewrite_pos_in_exists /=; simpl_embed.
  }

(*
  d_have {-A
    (exists: (* m *)
      ((eventually^ ((self-event /\ on n, ((0, CSLSend ' n' ' (c, #0)) \in Fors)) /\
        eventually (on n', event[]<- CPLDeliver ' n ' #0))) \/
      ((self-event /\ on n, ((0, CSLSend ' n' ' (c, #0)) \in Fors)) /\
        eventually (on n', event[]<- CPLDeliver ' n ' #0)) \/
      (eventuallyp^ ((self-event /\ on n, ((0, CSLSend ' n' ' (c, #0)) \in Fors)) /\
        eventually (on n', event[]<- CPLDeliver ' n ' #0))))) ->
    ((eventually^ ((self-event /\ on n, ((0, CSLSend ' n' ' (c, m')) \in Fors)) /\
      eventually (on n', event[]<- CPLDeliver ' n ' m'))) \/
    ((self-event /\ on n, ((0, CSLSend ' n' ' (c, m)) \in Fors)) /\
      eventually (on n', event[]<- CPLDeliver ' n ' m)) \/
    (eventuallyp^ ((self-event /\ on n, ((0, CSLSend ' n' ' (c, m')) \in Fors)) /\
      eventually (on n', event[]<- CPLDeliver ' n ' m'))))
   -}.
  {
    d_have {-A
      (exists: (* m *)
        ((eventually^ ((self-event /\ on n, ((0, CSLSend ' n' ' (c, #0)) \in Fors)) /\
          eventually (on n', event[]<- CPLDeliver ' n ' #0))) \/
        ((self-event /\ on n, ((0, CSLSend ' n' ' (c, #0)) \in Fors)) /\
          eventually (on n', event[]<- CPLDeliver ' n ' #0)) \/
        (eventuallyp^ ((self-event /\ on n, ((0, CSLSend ' n' ' (c, #0)) \in Fors)) /\
          eventually (on n', event[]<- CPLDeliver ' n ' #0))))) ->
      (exists: (* m *)
        (eventually^ ((self-event /\ on n, ((0, CSLSend ' n' ' (c, #0)) \in Fors)) /\
          eventually (on n', event[]<- CPLDeliver ' n ' #0)))) \/
      (exists: (* m *)
        ((self-event /\ on n, ((0, CSLSend ' n' ' (c, #0)) \in Fors)) /\
          eventually (on n', event[]<- CPLDeliver ' n ' #0))) \/
      (exists: (* m *)
        eventuallyp^ ((self-event /\ on n, ((0, CSLSend ' n' ' (c, #0)) \in Fors)) /\
          eventually (on n', event[]<- CPLDeliver ' n ' #0)))
     -}.
    {
      set A1 := {-A eventually^ ((self-event /\ on n, ((0, CSLSend ' n' ' (c, #0)) \in Fors)) /\
        eventually on n', event[]<- CPLDeliver ' n ' #0) -}.
      set A2 := {-A ((self-event /\ on n, ((0, CSLSend ' n' ' (c, #0)) \in Fors)) /\
        eventually (on n', event[]<- CPLDeliver ' n ' #0)) -}.
      set A3 := {-A (eventuallyp^ ((self-event /\ on n, ((0, CSLSend ' n' ' (c, #0)) \in Fors)) /\
        eventually (on n', event[]<- CPLDeliver ' n ' #0))) -}.
      d_ifc.

      eapply DARewriteIffPL with
        (Arp := {-A exists: (* m *) (A1 \/ A2 \/ A3) -})
        (Arc := {-A (exists: (* m *) A1) \/ (exists: (* m *) A2) \/ (exists: (* m *) A3) -});
        first by eapply DSCut; first by repeat d_clear; eapply DSExistsDistributesOr3 with
          (A1 := A1)
          (A2 := A2)
          (A3 := A3);
          rewrite /is_assertion_closed /=; auto_in_seq_and.
      by simpl_embed.
    }

    d_ifc.
    set A1 := {-A eventually^ ((self-event /\ on n, ((0, CSLSend ' n' ' (c, #0)) \in Fors)) /\
      eventually on n', event[]<- CPLDeliver ' n ' #0) -}.
    set A2 := {-A ((self-event /\ on n, ((0, CSLSend ' n' ' (c, #0)) \in Fors)) /\
      eventually (on n', event[]<- CPLDeliver ' n ' #0)) -}.
    set A3 := {-A (eventuallyp^ ((self-event /\ on n, ((0, CSLSend ' n' ' (c, #0)) \in Fors)) /\
      eventually (on n', event[]<- CPLDeliver ' n ' #0))) -}.
    d_swap.
    eapply DSModusPonensP; first by d_head.
    admit.
  }

  d_swap.
  eapply DARewriteIfP; first by d_head.
  simpl_embed.
  do 2 (d_swap; d_clear).

  d_have {-A
    on n, event []-> CPLSend ' n' ' m =>>
    (self-event /\ on n, ((0, CSLSend ' n' ' (c, m)) \in Fors)) /\
      eventually on n', event[]<- CPLDeliver ' n ' m \/
    (self-event /\ on n, ((0, CSLSend ' n' ' (c, m)) \in Fors)) /\
      eventually^ ((self-event /\ on n, ((0, CSLSend ' n' ' (c, m')) \in Fors)) /\
      eventually on n', event[]<- CPLDeliver ' n ' m') \/
    (self-event /\ on n, ((0, CSLSend ' n' ' (c, m)) \in Fors)) /\
      (self-event /\ on n, ((0, CSLSend ' n' ' (c, m)) \in Fors)) /\
      eventually on n', event[]<- CPLDeliver ' n ' m \/
    (self-event /\ on n, ((0, CSLSend ' n' ' (c, m)) \in Fors)) /\
      eventuallyp^ ((self-event /\ on n, ((0, CSLSend ' n' ' (c, m')) \in Fors)) /\
      eventually on n', event[]<- CPLDeliver ' n ' m')
   -}.
  {
    set D1 := {-A eventually on n', event[]<- CPLDeliver ' n ' m -}.
    set D2 := {-A eventually on n', event[]<- CPLDeliver ' n ' m' -}.

    set A1 := {-A self-event /\ on n, ((0, CSLSend ' n' ' (c, m)) \in Fors) -}.
    set A2 := {-A self-event /\ on n, ((0, CSLSend ' n' ' (c, m')) \in Fors) -}.

    set E1 := {-A eventually^ ((self-event /\ on n, ((0, CSLSend ' n' ' (c, m)) \in Fors)) /\
      eventually (on n', event[]<- CPLDeliver ' n ' m)) -}.
    set E2 := {-A eventually^ ((self-event /\ on n, ((0, CSLSend ' n' ' (c, m')) \in Fors)) /\
      eventually (on n', event[]<- CPLDeliver ' n ' m')) -}.

    set F1 := {-A eventuallyp^ ((self-event /\ on n, ((0, CSLSend ' n' ' (c, m)) \in Fors)) /\
      eventually (on n', event[]<- CPLDeliver ' n ' m)) -}.
    set F2 := {-A eventuallyp^ ((self-event /\ on n, ((0, CSLSend ' n' ' (c, m')) \in Fors)) /\
      eventually (on n', event[]<- CPLDeliver ' n ' m')) -}.

    set G1 := {-A (self-event /\ on n, ((0, CSLSend ' n' ' (c, m)) \in Fors)) /\
      eventually (on n', event[]<- CPLDeliver ' n ' m) -}.
    set G2 := {-A ((self-event /\ on n, ((0, CSLSend ' n' ' (c, m')) \in Fors)) /\
      eventually (on n', event[]<- CPLDeliver ' n ' m')) -}.

    eapply DARewriteIffPL with
      (Arp := {-A A1 /\ (D1 \/ E2 \/ G1 \/ F2) -})
      (Arc := {-A (A1 /\ D1) \/ (A1 /\ E2) \/ (A1 /\ G1) \/ (A1 /\ F2) -});
      first by eapply DSOrDistributesAnd4.
    by simpl_embed.
  }

  d_have {-A
    (self-event /\ on n, ((0, CSLSend ' n' ' (c, m)) \in Fors)) /\
      eventually^ ((self-event /\ on n, ((0, CSLSend ' n' ' (c, m')) \in Fors)) /\
        eventually on n', event []<- CPLDeliver ' n ' m') \/
    (self-event /\ on n, ((0, CSLSend ' n' ' (c, m)) \in Fors)) /\
      (self-event /\ on n, ((0, CSLSend ' n' ' (c, m)) \in Fors)) /\
      eventually on n', event []<- CPLDeliver ' n ' m \/
    (self-event /\ on n, ((0, CSLSend ' n' ' (c, m)) \in Fors)) /\
      eventuallyp^ ((self-event /\ on n, ((0, CSLSend ' n' ' (c, m')) \in Fors)) /\
        eventually on n', event []<- CPLDeliver ' n ' m') ->
    (self-event /\ on n, ((0, CSLSend ' n' ' (c, m)) \in Fors)) /\
      eventually^ (self-event /\ on n, ((0, CSLSend ' n' ' (c, m')) \in Fors)) \/
    (self-event /\ on n, ((0, CSLSend ' n' ' (c, m)) \in Fors)) /\
      eventually on n', event []<- CPLDeliver ' n ' m \/
    (self-event /\ on n, ((0, CSLSend ' n' ' (c, m)) \in Fors)) /\
      eventuallyp^ (self-event /\ on n, ((0, CSLSend ' n' ' (c, m')) \in Fors))
   -}.
  {
    set A1 := {-A self-event /\ on n, ((0, CSLSend ' n' ' (c, m)) \in Fors) -}.
    set B1 := {-A eventually on n', event[]<- CPLDeliver ' n ' m -}.

    d_have {-A
      eventually^ ((self-event /\ on n, ((0, CSLSend ' n' ' (c, m')) \in Fors)) /\
        eventually (on n', event[]<- CPLDeliver ' n ' m')) ->
      eventually^ ((self-event /\ on n, ((0, CSLSend ' n' ' (c, m')) \in Fors)))
     -}.
    {
      d_have {-A
        (self-event /\ on n, ((0, CSLSend ' n' ' (c, m')) \in Fors)) /\
          eventually on n', event []<- CPLDeliver ' n ' m' ->
        self-event /\ on n, ((0, CSLSend ' n' ' (c, m')) \in Fors)
       -}; first by d_ifc; d_splitp.
      d_ifc.
      eapply DARewriteIfP; first by d_head.
      by simpl_embed.
    }

    d_have {-A
      eventuallyp^ ((self-event /\ on n, ((0, CSLSend ' n' ' (c, m')) \in Fors)) /\
        eventually (on n', event[]<- CPLDeliver ' n ' m')) ->
      eventuallyp^ ((self-event /\ on n, ((0, CSLSend ' n' ' (c, m')) \in Fors)))
     -}.
    {
      d_have {-A
        ((self-event /\ on n, ((0, CSLSend ' n' ' (c, m')) \in Fors)) /\
          eventually (on n', event[]<- CPLDeliver ' n ' m')) ->
        (self-event /\ on n, ((0, CSLSend ' n' ' (c, m')) \in Fors))
       -}; first by d_ifc; d_splitp.
      d_ifc.
      eapply DARewriteIfP; first by d_head.
      by simpl_embed.
    }

    d_ifc.
    eapply DARewriteIfP; first by d_head.
    simpl_embed.

    set A2 := {-A self-event /\ on n, ((0, CSLSend ' n' ' (c, m')) \in Fors) -}.
    set B2 := {-A eventually on n', event[]<- CPLDeliver ' n ' m' -}.
    eapply DARewriteIfP; first by d_swap; d_head.
    simpl_embed.

    set A3 := {-A self-event /\ on n, ((0, CSLSend ' n' ' (c, m)) \in Fors) -}.
    set B3 := {-A eventually on n', event[]<- CPLDeliver ' n ' m -}.
    d_have {-A
      A3 /\ A3 /\ B3 -> A3 /\ B3
     -}.
    {
      d_ifc; d_splitp; d_splitc; first by d_head.
      by d_clear; d_splitp; d_clear.
    }

    d_swap; eapply DARewriteIfP; first by d_head.
    by simpl_embed; rewrite andbF.
  }

  d_have {-A
    on n, event []-> CPLSend ' n' ' m =>>
    (self-event /\ on n, ((0, CSLSend ' n' ' (c, m)) \in Fors)) /\
      eventually on n', event[]<- CPLDeliver ' n ' m \/
    (self-event /\ on n, ((0, CSLSend ' n' ' (c, m)) \in Fors)) /\
      eventually^ (self-event /\ on n, ((0, CSLSend ' n' ' (c, m')) \in Fors)) \/
    (self-event /\ on n, ((0, CSLSend ' n' ' (c, m)) \in Fors)) /\
      eventually on n', event[]<- CPLDeliver ' n ' m \/
    (self-event /\ on n, ((0, CSLSend ' n' ' (c, m)) \in Fors)) /\
      eventuallyp^ (self-event /\ on n, ((0, CSLSend ' n' ' (c, m')) \in Fors))
   -}.
  {
    d_swap.
    eapply DARewriteIfP; first by d_head.
    by simpl_embed; rewrite andbF.
  }
*)

  d_have {-A
    (on n, event []-> CPLSend ' n' ' m =>>
    (self-event /\ on n, ((0, CSLSend ' n' ' (c, m)) \in Fors)) /\
    (eventually on n', event []<- CPLDeliver ' n ' m \/
      exists:
        (self-event /\ on n, ((0, CSLSend ' n' ' (c, #0)) \in Fors)) /\
        eventually on n', event []<- CPLDeliver ' n ' #0))
   -}.
  {
    d_use_empty L37_1; d_forallp n; d_forallp n'; simpl_embed.
    d_ifp; first by d_splitc; d_assumption.
    d_forallp m; simpl_embed.
    (*
    d_have {-A
      self-event /\ on n, ((0, CSLSend ' n' ' (c, m)) \in Fors) =>>
      always^ ~(self-event /\ on n, ((0, CSLSend ' n' ' (c, m')) \in Fors))
     -}.
    {
      do 12 d_clear.
      d_use_empty L37_1;
        d_forallp n; d_forallp n';
        d_forallp m; d_forallp m';
        d_forallp c; d_forallp c';
        d_forallp r;
        simpl_embed.
      by d_ifp; first by d_splitc; d_assumption.
    }

    d_have {-A
      (self-event /\ on n, ((0, CSLSend ' n' ' (c, m)) \in Fors)) /\
      eventually^ (self-event /\ on n, ((0, CSLSend ' n' ' (c, m')) \in Fors)) ->
      AFalse
     -}.
    {
      d_ifc; d_splitp.
      eapply DARewriteEntailsP; first by d_swap; d_head.
      simpl_embed.

      d_have {-A
        ~ eventually^ (self-event /\ on n, ((0, CSLSend ' n' ' (c, m')) \in Fors))
       -}.
      {
        eapply DARewriteCongruentPR with
          (Arc := {-A always^ (~ (self-event /\ on n, ((0, CSLSend ' n' ' (c, m')) \in Fors))) -})
          (Arp := {-A ~ eventually^ (self-event /\ on n, ((0, CSLSend ' n' ' (c, m')) \in Fors)) -});
          first by eapply DTL114_1.
        by simpl_embed.
      }

      set F := {-A eventually^ (self-event /\ on n, ((0, CSLSend ' n' ' (c, m')) \in Fors)) -}.
      eapply DSCut; first by eapply DSNotImpliesFalse with (Ac := F).
      d_splitp; d_swap; d_clear; d_swap.
      eapply DARewriteIfP; first by d_head.
      simpl_embed.

      d_swap; d_rotate 3.
      eapply DARewriteIfP; first by d_rotate 16; d_head.
      by simpl_embed.
    }

    d_have {-A
      self-event /\ on n, ((0, CSLSend ' n' ' (c, m)) \in Fors) =>>
      alwaysp^ ~(self-event /\ on n, ((0, CSLSend ' n' ' (c, m')) \in Fors))
     -}.
    {
      do 14 d_clear.
      d_use_empty L37_2;
        d_forallp n; d_forallp n';
        d_forallp m; d_forallp m';
        d_forallp c; d_forallp c';
        d_forallp r;
        simpl_embed.
      by d_ifp; first by d_splitc; d_assumption.
    }

    d_have {-A
      (self-event /\ on n, ((0, CSLSend ' n' ' (c, m)) \in Fors)) /\
        eventuallyp^ (self-event /\ on n, ((0, CSLSend ' n' ' (c, m')) \in Fors)) ->
      AFalse
     -}.
    {
      d_ifc; d_splitp.
      eapply DARewriteEntailsP; first by d_swap; d_head.
      simpl_embed.

      d_have {-A
        ~ eventuallyp^ (self-event /\ on n, ((0, CSLSend ' n' ' (c, m')) \in Fors))
       -}.
      {
        eapply DARewriteCongruentPR with
          (Arc := {-A alwaysp^ (~ (self-event /\ on n, ((0, CSLSend ' n' ' (c, m')) \in Fors))) -})
          (Arp := {-A ~ eventuallyp^ (self-event /\ on n, ((0, CSLSend ' n' ' (c, m')) \in Fors)) -});
          first by eapply DTL114.
        by simpl_embed.
      }

      set F := {-A eventuallyp^ (self-event /\ on n, ((0, CSLSend ' n' ' (c, m')) \in Fors)) -}.
      eapply DSCut; first by eapply DSNotImpliesFalse with (Ac := F).
      d_splitp; d_swap; d_clear; d_swap.

      eapply DARewriteIfP; first by d_head.
      simpl_embed.
      d_swap; d_rotate 3.
      eapply DARewriteIfP; first by d_rotate 18; d_head.
      by simpl_embed.
    }

    d_swap; d_clear; d_rotate 4; d_swap; do 11 d_clear; d_rotate 5.
    eapply DARewriteIfP; first by d_rotate 2; d_head.
    simpl_embed; rewrite andbF.
    eapply DARewriteIfP; first by d_rotate 3; d_head.
    by simpl_embed; rewrite andbF.
    *)
    admit.
  }

  do 10 (d_swap; d_clear).
  d_have {-A
    (self-event /\ on n, ((0, CSLSend ' n' ' (c, m)) \in Fors)) /\
      eventually on n', event[]<- CPLDeliver ' n ' m \/
    AFalse \/
    (self-event /\ on n, ((0, CSLSend ' n' ' (c, m)) \in Fors)) /\
      eventually on n', event[]<- CPLDeliver ' n ' m \/
    AFalse ->
    (self-event /\ on n, ((0, CSLSend ' n' ' (c, m)) \in Fors)) /\
      eventually on n', event[]<- CPLDeliver ' n ' m \/
    (self-event /\ on n, ((0, CSLSend ' n' ' (c, m)) \in Fors)) /\
      eventually on n', event[]<- CPLDeliver ' n ' m -}.
  {
    d_ifc.
    d_orp; first by d_left.
    d_orp; first by d_false.
    by d_orp; first by d_left.
  }

  d_swap.
  eapply DARewriteIfP; first by d_head.
  simpl_embed.

  d_swap; d_clear.
  d_have {-A
    (self-event /\ on n, ((0, CSLSend ' n' ' (c, m)) \in Fors)) /\
      eventually on n', event[]<- CPLDeliver ' n ' m ->
    eventually on n', event[]<- CPLDeliver ' n ' m
   -}.
  {
    by d_ifc; d_splitp; d_assumption.
  }

  d_swap.
  set X := {-A (self-event /\ on n, ((0, CSLSend ' n' ' (c, m)) \in Fors)) /\
    eventually on n', event[]<- CPLDeliver ' n ' m -}.
  d_have {-A
    X \/ X -> X
   -}.
  {
    by d_ifc; d_orp.
  }

  d_swap.
  eapply DARewriteIfP; first by d_head.
  simpl_embed.

  d_swap; d_clear.
  eapply DARewriteIfP; first by d_head.
  by simpl_embed.
Admitted. (* TODO *)

(* Lemmas used in proving PL_2 *)

Lemma L43 Delta : Context Delta [::] ||- perfect_link, {-A
  forall: forall: forall: forall: forall: forall: forall: (* 6:n, 5:n', 4:m, 3:m', 2:c, 1:c', 0:r *)
    self (
      (#5, #2) \in TRight (Fs ' #6) /\
      eventuallyp on #6, event[0]<- CSLDeliver ' #5 ' (#2, #4) =>>
      Fn = #6 -> (CPLDeliver ' #5 ' #4) \notin Fois
    )
   -}.
Proof.
  (* Introduce context *)
  set C := perfect_link; rewrite -/C /empty_context.
  d_forallc n Hf_n; d_forallc n' Hf_n';
    d_forallc m Hf_m; d_forallc m' Hf_m';
    d_forallc c Hf_c; d_forallc c' Hf_c';
    d_forallc r Hf_r;
    simpl_embed.

  d_have {-A
    self (
      (n', c) \in TRight (Fs ' n) /\
      eventuallyp on n, event[0]<- CSLDeliver ' n' ' (c, m) =>>
      Fn = n -> (CPLDeliver ' n' ' m) \notin Fois
    )
   -}.
  {
    set A := {-A (n', c) \in TRight (Fs ' n) /\
      eventuallyp on n, event[0]<- CSLDeliver ' n' ' (c, m) ->
      Fn = n -> CPLDeliver ' n' ' m \notin Fois -}.
    eapply DSCut; first by apply DPInvSe with (A := A).

    (* request *)
    d_ifp.
      d_have {-A
        (forall: (* e *) event[]-> #0 =>> A) ->
        self (forall: (* e *) event[]-> #0 =>> A)
       -}; first by eapply DTL129.
      eapply DARewriteIfC; first by d_head.
      simpl_embed.
      d_forallc e Hf_e; simpl_embed.
      d_clear.

      d_use DPIR; d_forallp e; d_evalp.
      d_have {-A
        ((Fs' ' Fn, Fors, Fois) =
          let: (#, #) := Fs ' Fn
          in: let: CPLSend ' # ' # := e
            in: let: # := #2.+1
              in: let: # := (0, CSLSend ' #1 ' (#0, #2))
                in: (#1, #5, [#0], [])) ->
        A
       -}.
      {
        d_ifc.
        d_destructp (fun t => {-A (Fs' ' Fn, Fors, Fois) = t -});
          d_existsp r_ Hf_r_; d_existsp c_ Hf_c_; simpl_embed;
          d_splitp; d_swap; d_substp; d_evalp.
        d_destructp (fun t => {-A (Fs' ' Fn, Fors, Fois) = t -});
          d_existsp m_ Hf_m_; d_existsp n'_ Hf_n'_; simpl_embed;
          d_splitp; d_swap; d_substp; distinguish_variables; d_evalp.
        d_destructpairp; repeat d_splitp.
        repeat d_ifc.
        d_rotate 4; d_substc; d_notc.
        by d_evalp.
      }

      d_swap.
      eapply DARewriteIfP; first by d_head.
      simpl_embed.
      d_evalp.
      by [].

    (* indication *)
    d_ifp.
      d_have {-A
        (forall: forall: (* 1:i, 0:e *)
          event[#1]<- #0 =>> A) ->
        self (forall: forall: (* 1:i, 0:e *)
          event[#1]<- #0 =>> A)
       -}; first by eapply DTL129.
      eapply DARewriteIfC; first by d_head.
      simpl_embed.
      d_forallc i Hf_i; d_forallc e Hf_e; simpl_embed.
      d_clear.

      d_use DPII; d_forallp i; d_forallp e; d_evalp.

      d_have {-A
        ((Fs' ' Fn, Fors, Fois) =
          let: (#, #) := Fs ' Fn
          in: let: (0, CSLDeliver ' # ' (#, #)) := 
            (i, e)
            in: if: (#(0), #(1)) \in #(4) then: (Fs ' Fn, [ ], [ ])
              else: let: # := #(4) \union [(#(0), #(1))]
                in: let: # := CPLDeliver ' #(1) ' #(3)
                  in: (#(5), #(1), [ ], [#(0)])) ->
        A
       -}.
      {
        d_ifc.
        d_destructp (fun t => {-A (Fs' ' Fn, Fors, Fois) = t -});
          d_existsp r_ Hf_r_; d_existsp c'_ Hf_c'_; simpl_embed;
          d_splitp; d_swap; d_substp; d_evalp.
        d_destructp (fun t => {-A (Fs' ' Fn, Fors, Fois) = t -});
          d_existsp m_ Hf_m_; d_existsp c_ Hf_c_; d_existsp n_ Hf_n_; simpl_embed;
          d_splitp; d_swap; d_substp; distinguish_variables; d_evalp.
        d_destructp (fun t => {-A (Fs' ' Fn, Fors, Fois) = t -});
          d_orp; d_splitp; d_swap; d_substp; d_evalp;
          d_destructpairp; repeat d_splitp.
        - by repeat d_ifc; d_rotate 4; d_substc; d_notc; d_evalp.
        repeat d_ifc; d_notc.
        do 4 (d_swap; d_rotate 1); d_substp.
        eapply DSCut; first by eapply DAPNotInCons.
        d_forallp {-t CPLDeliver ' n' ' m -};
          d_forallp {-t CPLDeliver ' n ' m -};
          d_forallp {-t [] -};
          simpl_embed.
        d_splitp; d_clear; d_ifp.
          d_splitc; first by
           d_notc; eapply DSEqualEvent; d_splitp; eapply DSNotEqualP;
            move/norP: Hf_n' => [H _]; move/eqP: H => H;
            case=> X; by case: H.
          by d_evalc.
        d_notp.
        d_in_cons_pl; simpl_embed; d_orp; last by d_evalp.
        apply DSEqualEvent; d_splitp.
        admit.
      }

      d_swap.
      eapply DARewriteIfP; first by d_head.
      simpl_embed.
      by d_evalp.

    (* periodic *)
    d_ifp.
      d_have {-A
        (event[]~> periodic_event.PE =>> A) ->
        self (event[]~> periodic_event.PE =>> A)
       -}; first by eapply DTL129.
      eapply DARewriteIfC; first by d_head.
      simpl_embed.
      d_clear.

      d_use DPPe.
      d_have {-A
        ((Fs' ' Fn, Fors, Fois) = periodic C ' Fn ' (Fs ' Fn)) ->
        A
       -}.
      {
        d_ifc.
        d_evalp.
        d_destructpairp; repeat d_splitp.
        repeat d_ifc; d_notc.
        do 4 (d_swap; d_rotate 1); d_substp.
        eapply DSCut; first by eapply DAPInNil.
        d_forallp {-t CPLDeliver ' n' ' m -}.
        simpl_embed.
        by d_notp.
      }

      d_swap.
      eapply DARewriteIfP; first by d_head.
      simpl_embed.
      by d_evalp.

    by d_head.
  }

  by d_head.
Qed.

Lemma L42 Delta : Context Delta [::] ||- perfect_link, {-A
  forall: forall: forall: (* 2:n, 1:n', 0:m *)
    self (
      on #2, (CPLDeliver ' #1 ' #0 \in Fois) =>>
      always^ (Fn = #2 -> CPLDeliver ' #1 ' #0 \notin Fois) /\
      alwaysp^ (Fn = #2 -> CPLDeliver ' #1 ' #0 \notin Fois)
    )
   -}.
Proof.
  (* Introduce context *)
  set C := perfect_link; rewrite -/C /empty_context.
  d_forallc n Hf_n; d_forallc n' Hf_n';
    d_forallc m Hf_m;
    simpl_embed.

  (* By InvLSE *)
  d_have {-A
    exists: (* c *)
    self always (
      on n, (CPLDeliver ' n' ' m \in Fois) ->
      ((n', #0) \in TRight (Fs' ' n)) /\
      on n, event[0]<- CSLDeliver ' n' ' (#0, m)
    )
   -}.
  {
    eapply DSCut; first by apply DSEmptyContext; apply DPInvLSE with
      (A := {-A
          exists: (* c *)
          (on n, (CPLDeliver ' n' ' m \in Fois)) ->
          ((n', #0) \in TRight (Fs' ' n)) /\
          on n, event[0]<- CSLDeliver ' n' ' (#0, m)
         -}); first by repeat constructor.

    (* request *)
    d_ifp.
      d_forallc e Hf_e; simpl_embed.
      d_ifc; d_splitp; d_swap; d_evalp.
      d_destructp (fun t => {-A (Fs' ' Fn, Fors, Fois) = t -}).
        d_existsp r Hf_r; d_existsp c Hf_c; d_splitp; d_swap; d_substp; d_evalp.
      d_destructp (fun t => {-A (Fs' ' Fn, Fors, Fois) = t -});
        d_existsp pm Hf_pm; d_existsp n'_ Hf_n'_; d_splitp; d_swap;
        d_substp; distinguish_variables; d_evalp.
      d_existsc c; simpl_embed.
      d_ifc; d_swap.
      d_destructpairp; repeat d_splitp.
      d_rotate 3.
      do 5 (d_swap; d_rotate 1); d_substp; d_splitp; d_swap.
      by d_evalp.

    (* indication *)
    d_ifp.
      d_forallc i Hf_i; d_forallc e Hf_e; simpl_embed.
      d_ifc; d_splitp; d_swap; d_evalp.
      d_destructp (fun t => {-A (Fs' ' Fn, Fors, Fois) = t -});
        d_existsp r Hf_r; d_existsp c Hf_c; d_splitp; d_swap; d_substp; d_evalp.
      d_destructp (fun t => {-A (Fs' ' Fn, Fors, Fois) = t -});
        d_existsp m_ Hf_m_; d_existsp c_ Hf_c_; d_existsp n'_ Hf_n'_;
        d_splitp; d_swap; d_substp; distinguish_variables; d_evalp.
      d_destructp (fun t => {-A (Fs' ' Fn, Fors, Fois) = t -}).

      by d_orp; d_splitp; d_swap; d_substp; d_evalp;
        d_destructpairp; repeat d_splitp;
        d_existsc c; simpl_embed;
        d_ifc; do 2 (d_swap; d_rotate 1); d_substp; d_evalp;
        distinguish_variables; d_splitp; d_clear.

    (* periodic *)
    d_ifp.
      d_ifc; d_splitp; d_swap; d_evalp.
      d_destructpairp; repeat d_splitp.
      d_existsc 0; simpl_embed. (* Any c will work *)
      d_ifc.
      d_splitp; d_clear.
      by do 2 (d_swap; d_clear); d_substp; d_evalp.

    admit.
  }
  d_existsp c Hf_c.

  (* By lemma 87 *)
  d_have {-A
    self (
      on n, (CPLDeliver ' n' ' m \in Fois) =>>
      ((n', c) \in TRight (Fs' ' n)) /\
      eventuallyp (on n, event[0]<- CSLDeliver ' n' ' (c, m))
    )
   -}.
  {
    eapply DARewriteEntailsP with
      (Arp := {-A on n, event[0]<- CSLDeliver ' n' ' (c, m) -})
      (Arc := {-A eventuallyp (on n, event[0]<- CSLDeliver ' n' ' (c, m)) -});
      first by eapply DTL87.
    by simpl_embed; rewrite andbF.
  }

  (* By lemma 43 *)
  d_have {-A
    self (
      (n', c) \in TRight (Fs ' n) /\
      eventuallyp on n, event[0]<- CSLDeliver ' n' ' (c, m) =>>
      Fn = n -> CPLDeliver ' n' ' m \notin Fois
    )
   -}.
  {
    do 2 d_clear.
    d_use_empty L43.
  forall: forall: forall: forall: forall: forall: forall: (* 6:n, 5:n', 4:m, 3:m', 2:c, 1:c', 0:r *)
    d_forallp n; d_forallp n'; d_forallp m; d_forallp c; simpl_embed.
      d_forallp m;
      d_forallp c; d_forallp c';
      d_forallp r.
    by simpl_embed.
  }

  (* By InvSSe *)
  d_have {-A
    self (
      (n', c) \in TRight (Fs ' n) =>>
      always ((n', c) \in TRight (Fs ' n))
    )
   -}.
  {
    eapply DSCut; first by repeat d_clear; apply DPInvSSe with
      (S0 := {-A forall: (* ts *) (n', c) \in TRight #0 -});
      [by auto_is_closed | by repeat constructor].
    d_forallp n; simpl_embed.

    (* request *)
    d_ifp.
      d_forallc s Hf_s; d_forallc e Hf_e; d_ifc; d_eval.
      d_destructc (fun t => {-A (n', c) \in t -});
        d_forallc r_ Hf_r_; d_forallc c_ Hf_c_; d_ifc; d_substc; d_evalc.
      admit.

    (* indication *)
    d_ifp.
      d_forallc s Hf_s; d_forallc i Hf_i; d_forallc e Hf_e; d_ifc; d_eval.
      d_destructc (fun t => {-A (n', c) \in t -});
        d_forallc r_ Hf_r_; d_forallc c_ Hf_c_; d_ifc; d_substc; d_evalc.
      admit.

    (* periodic *)
    d_ifp.
      by d_forallc s Hf_s; d_ifc; d_eval.

    by d_evalp.
  }

  (* By lemma 104 *)
  d_have {-A
    self (
      eventuallyp (on n, event[0]<- CSLDeliver ' n' ' (c, m)) =>>
        always (eventuallyp (on n, event[0]<- CSLDeliver ' n' ' (c, m)))
    )
   -}.
  {
    set A := {-A eventuallyp (on n, event[0]<- CSLDeliver ' n' ' (c, m)) -}.
    d_have {-A
      (A =>> always A) -> self (A =>> always A)
     -}; first by eapply DTL129.
    by d_ifp; first by eapply DTL104.
  }

  (* By (3) and (4) *)
  d_have {-A
    self (
      ((n', c) \in TRight (Fs ' n)) /\
      eventuallyp on n, event[0]<- CSLDeliver ' n' ' (c, m) =>>
      always (((n', c) \in TRight (Fs ' n)) /\
      eventuallyp on n, event[0]<- CSLDeliver ' n' ' (c, m))
    )
   -}.
  {
    set A := {-A (n', c) \in TRight (Fs ' n) -}.
    set B := {-A eventuallyp on n, event[0]<- CSLDeliver ' n' ' (c, m) -}.
    d_have {-A
      (A =>> always A) /\ (B =>> always B) ->
      (A /\ B =>> (always A) /\ (always B))
     -}.
    {
      d_ifc; d_splitp; d_splitc.
        d_ifc; d_splitp; d_rotate 2; d_splitp; d_swap; d_clear; d_swap;
          d_splitp; d_swap; d_clear; d_ifp; first by d_assumption.
        d_swap; d_ifp; first by d_assumption.
        d_splitc; d_assumption.
      d_splitp; d_clear; d_swap; d_splitp; d_clear.
      d_have {-A
        (A -> always A) /\ (B -> always B) ->
        (A /\ B -> always A /\ always B)
       -}.
      {
        d_ifc; d_ifc; d_swap; d_splitp; d_ifp; first by d_swap; d_splitp.
        d_splitc; first by d_head.
        by d_swap; d_ifp; first by d_swap; d_splitp; d_swap.
      }

      eapply DARewriteIfC; first by d_head.
      simpl_embed.
      eapply DARewriteCongruentCL; first by eapply DTL128_3 with
        (A := {-A A -> always A -})
        (B := {-A B -> always B -}).
      simpl_embed.

      by d_splitc; d_assumption.
    }

    eapply DARewriteCongruentPR with
      (Arc := {-A always A /\ always B -})
      (Arp := {-A always (A /\ B) -});
      first by eapply DTL128_1.
    simpl_embed.

    set A1 := {-A (n', c) \in TRight (Fs ' n) -}.
    set B1 := {-A eventuallyp on n, event[0]<- CSLDeliver ' n' ' (c, m) -}.
    eapply DARewriteIfC; first by d_head.
    simpl_embed.

    eapply DARewriteIffCL with
      (Arp := {-A self ((A1 =>> always A1) /\ (B1 =>> always B1)) -})
      (Arc := {-A self ((A1 =>> always A1)) /\ self ((B1 =>> always B1)) -});
      first by eapply DTL130.
    simpl_embed.

    by d_splitc; d_assumption.
  }

  (* By lemma 97 on (5) and (2) *)
  d_have {-A
    self (
      (n', c) \in TRight (Fs ' n) /\
      eventuallyp on n, event[0]<- CSLDeliver ' n' ' (c, m) =>>
      always (Fn = n -> CPLDeliver ' n' ' m \notin Fois)
    )
   -}.
  {
    set A := {-A (n', c) \in TRight (Fs ' n) -}.
    set B := {-A eventuallyp on n, event[0]<- CSLDeliver ' n' ' (c, m) -}.
    set D := {-A (Fn = n -> CPLDeliver ' n' ' m \notin Fois) -}.
    d_have {-A
      self (
        (A /\ B =>> always (A /\ B)) /\ (A /\ B =>> D) ->
        (A /\ B =>> always D)
      )
     -}.
    {
      d_have {-A
        ((A /\ B =>> always (A /\ B)) /\ (A /\ B =>> D) -> A /\ B =>> always D) ->
        self ((A /\ B =>> always (A /\ B)) /\ (A /\ B =>> D) -> A /\ B =>> always D)
       -}; first by eapply DTL129.

      by d_ifp; first by eapply DTL97 with
        (A1 := {-A A /\ B -})
        (A2 := {-A A /\ B -})
        (A3 := {-A D -}).
    }

    eapply DSCut; first by apply DTL131 with
      (A := {-A (A /\ B =>> always (A /\ B)) /\ (A /\ B =>> D) -})
      (B := {-A A /\ B =>> always D -}).
    d_ifp; first by d_head.

    d_ifp.
      eapply DARewriteIffCL; first by eapply DTL130 with
        (A := {-A (A /\ B =>> always (A /\ B)) -})
        (B := {-A (A /\ B =>> D) -}).
      simpl_embed.
      by d_splitc; d_assumption.

    by [].
  }

  (* By rule ASASe on (1) and (6) *)
  d_have {-A
    self ((on n, (CPLDeliver ' n' ' m \in Fois)) =>>
    always^ (Fn = n -> CPLDeliver ' n' ' m \notin Fois))
   -}.
  {
    eapply DSCut; first by repeat d_clear; eapply DPASASe with
      (S := {-A forall: (n', c) \in (TRight #0) /\
          eventuallyp on n, event[0]<- CSLDeliver ' n' ' (c, m)
         -})
      (A := {-A on n, (CPLDeliver ' n' ' m \in Fois) -})
      (A' := {-A (Fn = n -> CPLDeliver ' n' ' m \notin Fois) -});
      [by auto_is_closed].
    d_forallp n; d_evalp.
    d_ifp; first by d_assumption.
    by d_ifp; d_assumption.
  }

  d_have {-A
    (Fn = n -> CPLDeliver ' n' ' m \notin Fois) ->
    ~(on n, (CPLDeliver ' n' ' m \in Fois))
   -}.
  {
    repeat d_clear.
    d_ifc; d_notc.
    d_splitp; d_rotate 2; d_ifp; first by d_assumption.
    by d_substp; d_notp; d_assumption.
  }

  d_swap.
  eapply DARewriteIfP; first by d_head.
  simpl_embed.

  set P := {-A on n, (CPLDeliver ' n' ' m \in Fois) -}.
  d_have {-A
    self (P =>> alwaysp^ (~ P))
   -}.
  {
    eapply DARewriteIfP; first by apply DTL105_1 with (A := P).
    by simpl_embed.
  }

  d_have {-A
    self (
      P =>> always^ (~ P) /\ alwaysp^ (~ P)
    )
   -}.
  {
    d_have {-A
      (P =>> always^ (~ P)) /\ (P =>> alwaysp^ (~ P)) ->
      (P =>> always^ (~ P) /\ alwaysp^ (~ P))
     -}.
    {
      d_ifc; d_splitp; d_splitc.
        d_ifc; d_swap; d_splitp; d_splitc; first by d_ifp; d_assumption.
        by do 2 d_clear; d_swap; d_splitp; d_swap; d_clear; d_ifp.

      d_have {-A
        ((P -> always^ ~P) /\ (P -> alwaysp^ ~P)) ->
        (P ->  (always^ (~ P) /\ alwaysp^ (~ P)))
       -}.
      {
        d_ifc; d_ifc; d_swap; d_splitp; d_ifp; first by d_assumption.
        d_splitc; first by d_head.
        by d_swap; d_ifp; d_assumption.
      }

      eapply DARewriteIfC; first by d_head.
      simpl_embed.

      eapply DARewriteCongruentCL; first by eapply DTL128_3 with
        (A := {-A P -> always^ ~P -})
        (B := {-A P -> alwaysp^ (~ P) -}).
      simpl_embed.

      d_ifp; first by d_splitc; [d_splitp | d_swap; d_splitp]; d_assumption.
      d_splitc; first by d_swap; d_splitp; d_assumption.
      d_rotate 2; d_splitp; d_assumption.
    }

    eapply DARewriteIfC; first by d_head.
    simpl_embed.

    eapply DARewriteIffCL with
      (Arp := {-A self ((P =>> always^ (~ P)) /\ (P =>> alwaysp^ (~ P))) -})
      (Arc := {-A self ((P =>> always^ (~ P))) /\ self ((P =>> alwaysp^ (~ P))) -});
      first by eapply DTL130.
    simpl_embed.

    by d_splitc; d_assumption.
  }

  d_have {-A
    ~(on n, (CPLDeliver ' n' ' m \in Fois)) ->
    (Fn = n -> CPLDeliver ' n' ' m \notin Fois)
   -}; first by repeat d_clear; d_ifc; d_ifc; d_notc; d_rotate 2;
      d_notp; d_splitc; d_assumption.

  d_swap.
  eapply DARewriteIfC; first by d_swap; d_head.
  by simpl_embed.
Admitted.

Lemma L44 Delta : Context Delta [::] ||- perfect_link, {-A
  forall: forall: forall: forall: forall: (* 4:n, 3:n', 2:m, 1:c, 0:c' *)
    correct #4 /\ correct #3 ->
    (on #3, event[]-> CPLSend ' #4 ' #2 =>>
      alwaysp^ (~ on #3, event[]-> CPLSend ' #4 ' #2)) ->
    self (
      on #4, event[0]<- CSLDeliver ' #3 ' (#1, #2) /\
      eventuallyp on #4, event[0]<- CSLDeliver ' #3 ' (#0, #2) =>>
      #1 = #0
    )
   -}.
Proof.
  (* Introduce context *)
  set C := perfect_link; rewrite -/C /empty_context.
  d_forallc n Hf_n; d_forallc n' Hf_n';
    d_forallc m Hf_m;
    d_forallc c Hf_c; d_forallc c' Hf_c';
    simpl_embed.
  d_ifc; d_splitp; d_ifc.

  (* By SL_2 *)
  d_have {-A
    forall: forall: forall: (* 2:n, 1:n', 0:m *)
    on #2, event[0]<- CSLDeliver ' #1 ' #0 <~
    on #1, event[0]-> CSLSend ' #2 ' #0
   -}; first by d_use_empty PL_SL_2.
  d_forallp n; d_forallp n'; d_forallp {-t (c, m) -}; simpl_embed.

  (* By OR' *)
  d_have {-A
    (on n', event[0]-> CSLSend ' n ' (c, m)) =>>
    eventuallyp (on n', ((0, (CSLSend ' n ' (c, m))) \in Fors) /\ self-event)
   -}.
  {
    d_swap; d_clear.
    d_use DPOR';
      d_forallp n'; d_forallp 0; d_forallp {-t CSLSend ' n ' (c, m) -};
      simpl_embed.
    eapply DARewriteIfP with
      (Arp := {-A self-event /\ on n', ((0, CSLSend ' n ' (c, m)) \in Fors) -})
      (Arc := {-A on n', ((0, (CSLSend ' n ' (c, m))) \in Fors) /\ self-event -}).
    {
      d_ifc; d_splitc;
        first by d_splitp; d_swap; d_splitp; d_swap; d_splitc; d_assumption.
      by d_splitp.
    }
    simpl_embed.

    eapply DARewriteIfP; first by apply DTL123 with
      (A := {-A on n', ((0, (CSLSend ' n ' (c, m))) \in Fors) /\ self-event -}).
    by simpl_embed.
  }

  (* By InvL *)
  d_have {-A
    (on n', ((0, (CSLSend ' n ' (c, m))) \in Fors) /\ self-event) =>>
    (on n', event[]-> CPLSend ' n ' m) /\ (TLeft (Fs' ' n) = c)
   -}.
  {
    eapply DSCut; first by eapply DSEmptyContext; apply DPInvL with
      (A := {-A on n', ((0, CSLSend ' n ' (c, m)) \in Fors) ->
        ((on n', event[]-> CPLSend ' n ' m) /\ (TLeft (Fs' ' n) = c)) -});
      first by repeat constructor.

    (* request *)
    d_ifp.
      d_forallc e Hf_e; simpl_embed.
      d_ifc; d_splitp; d_swap; d_evalp.
      d_destructp (fun t => {-A (Fs' ' Fn, Fors, Fois) = t -});
        d_existsp r Hf_r; d_existsp c_ Hf_c_; d_splitp; d_swap; d_substp; d_evalp.
      d_destructp (fun t => {-A (Fs' ' Fn, Fors, Fois) = t -});
        d_existsp m_ Hf_m_; d_existsp n_ Hf_n_; d_splitp; d_swap;
        d_substp; distinguish_variables; d_evalp.
      d_destructpairp; repeat d_splitp.
      d_ifc; d_splitp.
      d_swap; do 2 (d_swap; d_rotate 1); d_substp.
      by d_evalp; rewrite andbF /=.

    (* indication *)
    d_ifp.
      d_forallc i Hf_i; d_forallc e Hf_e; simpl_embed.
      d_ifc; d_splitp; d_swap; d_evalp.
      d_destructp (fun t => {-A (Fs' ' Fn, Fors, Fois) = t -});
        d_existsp r Hf_r; d_existsp c_ Hf_c_; d_splitp; d_swap; d_substp; d_evalp.
      d_destructp (fun t => {-A (Fs' ' Fn, Fors, Fois) = t -});
        d_existsp m' Hf_m'; d_existsp c'_ Hf_c'_; d_existsp n'_ Hf_n'_;
        d_splitp; d_swap; d_substp; distinguish_variables; d_evalp.
      d_destructp (fun t => {-A (Fs' ' Fn, Fors, Fois) = t -}).
      by d_orp; d_splitp; d_swap; d_substp; d_evalp; d_ifc; d_swap;
        d_destructpairp; repeat d_splitp;
        d_swap; do 2 (d_swap; d_rotate 1); d_swap; d_substp; d_splitp;
        d_clear; d_evalp.

    (* periodic *)
    d_ifp.
      d_ifc; d_splitp; d_swap; d_evalp.
      d_destructpairp; repeat d_splitp.
      by d_ifc; d_splitp; d_swap; do 2 (d_swap; d_rotate 1); d_substp; d_evalp.

    d_splitp; d_swap; d_clear.
    eapply DTGeneralization; first by repeat constructor.
    d_ifc; d_splitp; d_rotate 2; d_ifp; first by d_assumption.
    by d_ifp; first by d_assumption.
  }

  (* By lemma 86 and lemma 96 on (1), (2), and (3) *)
  d_have {-A
    (on n, event[0]<- CSLDeliver ' n' ' (c, m)) =>>
    eventuallyp (on n', event[]-> CPLSend ' n ' m /\ TLeft (Fs' ' n) = c)
   -}.
  {
    eapply DSCut; first by eapply DTL96_2 with
      (A1 := {-A on n, event[0]<- CSLDeliver ' n' ' (c, m) -})
      (A2 := {-A on n', event[0]-> CSLSend ' n ' (c, m) -})
      (A3 := {-A eventuallyp (on n', ((0, CSLSend ' n ' (c, m)) \in Fors) /\ self-event) -}).
    d_ifp; first by d_splitc; d_assumption.
    eapply DARewriteCongruentPR; first by apply DTL83_1 with
      (A := {-A on n', ((0, CSLSend ' n ' (c, m)) \in Fors) /\ self-event -}).
    simpl_embed.

    eapply DSCut; first by eapply DTL96_2 with
      (A1 := {-A on n, event[0]<- CSLDeliver ' n' ' (c, m) -})
      (A2 := {-A on n', ((0, CSLSend ' n ' (c, m)) \in Fors) /\ self-event -})
      (A3 := {-A on n', event[]-> CPLSend ' n ' m /\ TLeft (Fs' ' n) = c -}).
    by d_ifp; first by d_splitc; d_assumption.
  }

  (* By rule SInv on (4) *)
  d_have {-A
    self (
      (on n, event[0]<- CSLDeliver ' n' ' (c, m)) =>>
      eventuallyp (on n', event[]-> CPLSend ' n ' m /\ TLeft (Fs' ' n) = c)
    )
   -}.
  {
    eapply DARewriteIfP with
      (Arp := {-A self (
          (on n, event[0]<- CSLDeliver ' n' ' (c, m)) =>>
          eventuallyp (on n', event[]-> CPLSend ' n ' m /\ TLeft (Fs' ' n) = c)
        ) -})
      (Arc := restrict_assertion
        {-A self-event -}
        {-A (on n, event[0]<- CSLDeliver ' n' ' (c, m)) =>>
            eventuallyp (on n', event[]-> CPLSend ' n ' m /\ TLeft (Fs' ' n) = c)
           -}); first by eapply DPSInv_1.
    simpl_embed.

    d_have {-A
      (on n, event[0]<- CSLDeliver ' n' ' (c, m) <~
        (on n', event[]-> CPLSend ' n ' m) /\ TLeft (Fs' ' n) = c) ->
      self (
        on n, event[0]<- CSLDeliver ' n' ' (c, m) <~
        (on n', event[]-> CPLSend ' n ' m) /\ TLeft (Fs' ' n) = c
      )
     -}; first by eapply DTL129.
    by d_ifp.
  }

  (* Similarly for c' *)
  d_have {-A
    (on n, event[0]<- CSLDeliver ' n' ' (c', m)) =>>
    eventuallyp (on n', event[]-> CPLSend ' n ' m /\ TLeft (Fs' ' n) = c')
   -}.
  {
    do 5 d_clear.
    d_have {-A
      forall: forall: forall: (* 2:n, 1:n', 0:m *)
      on #2, event[0]<- CSLDeliver ' #1 ' #0 <~
      on #1, event[0]-> CSLSend ' #2 ' #0
     -}; first by by d_use_empty PL_SL_2.
    d_forallp n; d_forallp n'; d_forallp {-t (c', m) -}; simpl_embed.

    (* By OR' *)
    d_have {-A
      (on n', event[0]-> CSLSend ' n ' (c', m)) =>>
      eventuallyp (on n', ((0, (CSLSend ' n ' (c', m))) \in Fors) /\ self-event)
     -}.
    {
      d_use DPOR';
        d_forallp n'; d_forallp 0; d_forallp {-t CSLSend ' n ' (c', m) -};
        simpl_embed.
      eapply DARewriteIfP with
        (Arp := {-A self-event /\ on n', ((0, CSLSend ' n ' (c', m)) \in Fors) -})
        (Arc := {-A on n', ((0, (CSLSend ' n ' (c', m))) \in Fors) /\ self-event -}).
      {
        d_ifc; d_splitc; first by d_splitp; d_swap; d_splitp; d_swap; d_splitc;
          d_assumption.
        by d_splitp.
      }
      simpl_embed.
      eapply DARewriteIfP; first by apply DTL123 with
        (A := {-A on n', ((0, (CSLSend ' n ' (c', m))) \in Fors) /\ self-event -}).
      by simpl_embed.
    }

    (* By InvL *)
    d_have {-A
      (on n', ((0, (CSLSend ' n ' (c', m))) \in Fors) /\ self-event) =>>
      (on n', event[]-> CPLSend ' n ' m) /\ (TLeft (Fs' ' n) = c')
     -}.
    {
      eapply DSCut; first by eapply DSEmptyContext; apply DPInvL with
        (A := {-A on n', ((0, CSLSend ' n ' (c', m)) \in Fors) ->
          ((on n', event[]-> CPLSend ' n ' m) /\ (TLeft (Fs' ' n) = c')) -});
        first by repeat constructor.

      (* request *)
      d_ifp.
        d_forallc e Hf_e; simpl_embed.
        d_ifc; d_splitp; d_swap; d_evalp.
        d_destructp (fun t => {-A (Fs' ' Fn, Fors, Fois) = t -});
          d_existsp r Hf_r; d_existsp c'_ Hf_c'_; d_splitp; d_swap; d_substp; d_evalp.
        d_destructp (fun t => {-A (Fs' ' Fn, Fors, Fois) = t -});
          d_existsp m_ Hf_m_; d_existsp n_ Hf_n_; d_splitp; d_swap;
          d_substp; distinguish_variables; d_evalp.
        d_destructpairp; repeat d_splitp.
        d_ifc; d_splitp.
        d_swap; do 2 (d_swap; d_rotate 1); d_substp.
        by d_evalp; rewrite andbF /=.

      (* indication *)
      d_ifp.
        d_forallc i Hf_i; d_forallc e Hf_e; simpl_embed.
        d_ifc; d_splitp; d_swap; d_evalp.
        d_destructp (fun t => {-A (Fs' ' Fn, Fors, Fois) = t -});
          d_existsp r Hf_r; d_existsp c'_ Hf_c'_; d_splitp; d_swap; d_substp; d_evalp.
        d_destructp (fun t => {-A (Fs' ' Fn, Fors, Fois) = t -});
          d_existsp m' Hf_m'; d_existsp c_ Hf_c_; d_existsp n'_ Hf_n'_;
          d_splitp; d_swap; d_substp; distinguish_variables; d_evalp.
        d_destructp (fun t => {-A (Fs' ' Fn, Fors, Fois) = t -}).
        by d_orp; d_splitp; d_swap; d_substp; d_evalp; d_ifc; d_swap;
          d_destructpairp; repeat d_splitp;
          d_swap; do 2 (d_swap; d_rotate 1); d_swap; d_substp; d_splitp;
          d_clear; d_evalp.

      (* periodic *)
      d_ifp.
        d_ifc; d_splitp; d_swap; d_evalp.
        d_destructpairp; repeat d_splitp.
        by d_ifc; d_splitp; d_swap; do 2 (d_swap; d_rotate 1); d_substp; d_evalp.

      d_splitp; d_swap; d_clear.
      eapply DTGeneralization; first by repeat constructor.
      d_ifc; d_splitp; d_rotate 2; d_ifp; first by d_assumption.
      by d_ifp; first by d_assumption.
    }

    (* By lemma 86 and lemma 96 *)
    d_have {-A
      (on n, event[0]<- CSLDeliver ' n' ' (c', m)) =>>
      eventuallyp (on n', event[]-> CPLSend ' n ' m /\ TLeft (Fs' ' n) = c')
     -}.
    {
      eapply DSCut; first by eapply DTL96_2 with
        (A1 := {-A on n, event[0]<- CSLDeliver ' n' ' (c', m) -})
        (A2 := {-A on n', event[0]-> CSLSend ' n ' (c', m) -})
        (A3 := {-A eventuallyp (on n', ((0, CSLSend ' n ' (c', m)) \in Fors) /\ self-event) -}).
      d_ifp; first by d_splitc; d_assumption.
      eapply DARewriteCongruentPR; first by apply DTL83_1 with
        (A := {-A on n', ((0, CSLSend ' n ' (c', m)) \in Fors) /\ self-event -}).
      simpl_embed.

      eapply DSCut; first by eapply DTL96_2 with
        (A1 := {-A on n, event[0]<- CSLDeliver ' n' ' (c', m) -})
        (A2 := {-A on n', ((0, CSLSend ' n ' (c', m)) \in Fors) /\ self-event -})
        (A3 := {-A on n', event[]-> CPLSend ' n ' m /\ TLeft (Fs' ' n) = c' -}).
      by d_ifp; first by d_splitc; d_assumption.
    }

    by d_head.
  }

  (* By rule SInv on (4) *)
  d_have {-A
    self (
      (on n, event[0]<- CSLDeliver ' n' ' (c', m)) =>>
      eventuallyp (on n', event[]-> CPLSend ' n ' m /\ TLeft (Fs' ' n) = c')
    )
   -}.
  {
    d_have {-A
      (on n, event[0]<- CSLDeliver ' n' ' (c', m) <~
      (on n', event[]-> CPLSend ' n ' m) /\ TLeft (Fs' ' n) = c') ->
      self (on n, event[0]<- CSLDeliver ' n' ' (c', m) <~
      (on n', event[]-> CPLSend ' n ' m) /\ TLeft (Fs' ' n) = c')
     -}; first by eapply DTL129.
    by d_ifp.
  }

  d_have {-A
    eventuallyp (on n', event[]-> CPLSend ' n ' m /\ TLeft (Fs' ' n) = c) /\
    eventuallyp (on n', event[]-> CPLSend ' n ' m /\ TLeft (Fs' ' n) = c') =>>
    c = c'
   -}.
  {
    set B1 := {-A on n', event[]-> CPLSend ' n ' m -}.
    set C1 := {-A TLeft (Fs' ' n) = c -}.
    set C2 := {-A TLeft (Fs' ' n) = c' -}.
    d_have {-A
      eventuallyp (B1 /\ C1) /\ eventuallyp (B1 /\ C2) =>>
      eventuallyp ((B1 /\ C1) /\ eventuallyp (B1 /\ C2)) \/
      eventuallyp ((B1 /\ C2) /\ eventuallyp (B1 /\ C1))
     -}.
    {
      by eapply DSCut; first by eapply DTL102_2 with
        (A1 := {-A on n', event[]-> CPLSend ' n ' m /\ TLeft (Fs' ' n) = c -})
        (A2 := {-A on n', event[]-> CPLSend ' n ' m /\ TLeft (Fs' ' n) = c' -}).
    }

    set P1 := {-A eventuallyp ((B1 /\ C1) /\ eventuallyp (B1 /\ C2)) -}.
    set P2 := {-A eventuallyp ((B1 /\ C2) /\ eventuallyp (B1 /\ C1)) -}.
    d_have {-A
      eventuallyp ((B1 /\ C1)) /\ eventuallyp (B1 /\ C2) =>>
      eventuallyp (B1 /\ C1 /\ eventuallyp C2) \/
      eventuallyp (B1 /\ C2 /\ eventuallyp C1)
     -}.
    {
      d_have {-A
        B1 /\ C1 -> (alwaysp^ (~ B1)) /\ C1
       -}.
      {
        d_ifc.
        eapply DARewriteEntailsP with
          (Arp := {-A B1 -})
          (Arc := {-A alwaysp^ (~ B1) -}); first by d_assumption.
        by simpl_embed.
      }

      d_have {-A
        P1 -> eventuallyp ((alwaysp^ (~ B1) /\ C1) /\ eventuallyp (B1 /\ C2))
       -}.
      {
        d_ifc.
        eapply DARewriteIfP; first by d_head.
        by simpl_embed; rewrite /eq_op /= !eq_refl !andTb /eq_op /= /eq_op /=;
          distinguish_variables.
      }
      d_swap; d_clear; d_swap.

      eapply DARewriteIfP; first by d_head.
      simpl_embed; rewrite /eq_op /= !eq_refl !andTb /eq_op /= /eq_op /=;
        distinguish_variables.
      d_swap; d_clear.
      set P1' := {-A eventuallyp ((alwaysp^ (~ B1) /\ C1) /\ eventuallyp (B1 /\ C2)) -}.
      set P2' := {-A eventuallyp ((B1 /\ C2) /\ eventuallyp (B1 /\ C1)) -}.
      d_have {-A
        eventuallyp (B1 /\ C2) ->
        eventuallyp B1 /\ eventuallyp C2
       -}.
      {
        d_ifc.
        eapply DARewriteEntailsP; first by apply DTL127_5 with
          (A := B1)
          (B := C2).
        by simpl_embed.
      }
      d_swap; eapply DARewriteIfP; first by d_head.
      simpl_embed; rewrite /eq_op /= !eq_refl !andTb /eq_op /= /eq_op /=;
        distinguish_variables.

      set P1'' := {-A eventuallyp ((alwaysp^ (~ B1) /\ C1) /\
        eventuallyp B1 /\ eventuallyp C2) -}.
      set P2'' := {-A eventuallyp ((B1 /\ C2) /\ eventuallyp (B1 /\ C1)) -}.
      d_have {-A
        (alwaysp^ (~ B1) /\ C1) /\ eventuallyp B1 /\ eventuallyp C2 ->
        (eventuallyp B1 /\ alwaysp^ (~ B1)) /\ C1 /\ eventuallyp C2
       -}.
      {
        d_ifc.
        d_splitp; d_splitp; d_splitc; first by d_rotate 2; d_splitp; d_splitc;
          d_assumption.
        d_splitc; first by d_assumption.
        by d_rotate 2; d_splitp; d_assumption.
      }
      d_swap; eapply DARewriteIfP; first by d_head.
      simpl_embed.

      set F1 := {-A (eventuallyp B1 /\ alwaysp^ (~ B1)) /\ C1 /\ eventuallyp C2 -}.
      set G1 := {-A eventuallyp ((B1 /\ C2) /\ eventuallyp (B1 /\ C1)) -}.
      d_have {-A
        (eventuallyp B1 /\ alwaysp^ (~ B1)) /\ C1 /\
        eventuallyp C2 -> B1 /\ C1 /\ eventuallyp C2
       -}.
      {
        d_ifc.
        eapply DARewriteEntailsP; first by apply DTL103_2 with (A := B1).
        by simpl_embed.
      }
      d_swap; eapply DARewriteIfP; first by d_head.
      simpl_embed.

      set F2 := {-A eventuallyp (B1 /\ C1 /\ eventuallyp C2) -}.
      set G2 := {-A eventuallyp ((B1 /\ C2) /\ eventuallyp (B1 /\ C1)) -}.
      d_have {-A
        eventuallyp ((B1 /\ C2) /\ eventuallyp (B1 /\ C1)) ->
        eventuallyp (B1 /\ C2 /\ eventuallyp C1)
       -}.
      {
        d_ifc.
        d_have {-A
          B1 /\ C2 -> (alwaysp^ (~ B1)) /\ C2
         -}.
        {
          d_ifc.
          eapply DARewriteEntailsP with
            (Arp := {-A B1 -})
            (Arc := {-A alwaysp^ (~ B1) -}); first by d_assumption.
          by simpl_embed.
        }

        d_have {-A
          P2 -> eventuallyp ((alwaysp^ (~ B1) /\ C2) /\ eventuallyp (B1 /\ C1))
         -}.
        {
          d_ifc.
          eapply DARewriteIfP; first by d_head.
          by simpl_embed; rewrite /eq_op /= !eq_refl !andTb /eq_op /= /eq_op /=;
            distinguish_variables.
        }
        d_swap; d_clear; d_swap.
        eapply DARewriteIfP; first by d_head.
        simpl_embed.

        d_swap; d_clear.
        d_have {-A
          eventuallyp (B1 /\ C1) ->
          eventuallyp B1 /\ eventuallyp C1
         -}.
        {
          d_ifc.
          eapply DARewriteEntailsP; first by apply DTL127_5 with
            (A := B1)
            (B := C1).
          by simpl_embed.
        }
        d_swap; eapply DARewriteIfP; first by d_head.
        simpl_embed.

        d_have {-A
          (alwaysp^ (~ B1) /\ C2) /\ eventuallyp B1 /\ eventuallyp C1 ->
          (eventuallyp B1 /\ alwaysp^ (~ B1)) /\ C2 /\ eventuallyp C1
         -}.
        {
          d_ifc.
          d_splitp; d_splitp; d_splitc; first by d_rotate 2; d_splitp; d_splitc;
            d_assumption.
          d_splitc; first by d_assumption.
          by d_rotate 2; d_splitp; d_assumption.
        }
        d_swap; eapply DARewriteIfP; first by d_head.
        simpl_embed.

        d_have {-A
          (eventuallyp B1 /\ alwaysp^ (~ B1)) /\ C2 /\
          eventuallyp C1 -> B1 /\ C2 /\ eventuallyp C1
         -}.
        {
          d_ifc.
          eapply DARewriteEntailsP; first by apply DTL103_2 with (A := B1).
          by simpl_embed.
        }
        d_swap; eapply DARewriteIfP; first by d_head.
        by simpl_embed.
      }

      d_have {-A
        F2 \/ eventuallyp ((B1 /\ C2) /\ eventuallyp (B1 /\ C1)) ->
        F2 \/ eventuallyp (B1 /\ C2 /\ eventuallyp C1)
       -}.
      {
        d_ifc; d_orp; first by d_left.
        d_right.
        eapply DARewriteIfP; first by d_head.
        by simpl_embed.
      }
      d_swap; d_clear; d_swap.
      eapply DARewriteIfP; first by d_head.
      by simpl_embed.
    }

    set E := {-A
        eventuallyp (B1 /\ C1 /\ eventuallyp C2) \/
        eventuallyp (B1 /\ C2 /\ eventuallyp C1)
       -}.

    d_have {-A
      eventuallyp (B1 /\ C1 /\ eventuallyp C2) \/
      eventuallyp (B1 /\ C2 /\ eventuallyp C1) ->
      eventuallyp (C1 /\ C2)
     -}.
    {
      set E1 := {-A
          eventuallyp (B1 /\ C1 /\ eventuallyp C2) \/
          eventuallyp (B1 /\ C2 /\ eventuallyp C1)
         -}.
      d_ifc.
      set D1 := {-A B1 /\ C1 /\ eventuallyp C2 -}.
      set D2 := {-A B1 /\ C2 /\ eventuallyp C1 -}.
      d_have {-A
        D1 -> C1 /\ C2
       -}.
      {
        d_ifc; d_splitp; d_swap; d_splitp; d_splitc; first by d_head.
        d_swap.
        eapply DSCut; first by eapply DTL133 with (P := {-A c = c' -}).
        admit.
      }
      d_swap; eapply DARewriteIfP; first by d_head.
      simpl_embed; rewrite /eq_op /= !eq_refl !andTb /eq_op /= /eq_op /=;
        distinguish_variables.

      set E2 := {-A
          eventuallyp (C1 /\ C2) \/ eventuallyp (B1 /\ C2 /\ eventuallyp C1)
         -}.
      d_have {-A
        D2 -> C1 /\ C2
       -}.
      {
        d_ifc. d_splitp. d_swap. d_splitp. d_swap. d_splitc.
        eapply DSCut; first by eapply DTL133 with (P := {-A c' = c -}).
        admit.
      }
      d_swap; eapply DARewriteIfP; first by d_head.
      simpl_embed.

      set E3 := {-A
          eventuallyp (C1 /\ C2) \/
          eventuallyp (C1 /\ C2)
         -}.
      set E4 := {-A
          eventuallyp (C1 /\ C2) \/
          eventuallyp (C1 /\ C2)
         -}.
      d_have {-A
        E4 -> eventuallyp (C1 /\ C2)
       -}; first by d_ifc; d_orp.
      d_swap; eapply DARewriteIfP; first by d_head.
      by simpl_embed.
    }

    set E5 := {-A
        eventuallyp (B1 /\ C1 /\ eventuallyp C2) \/
        eventuallyp (B1 /\ C2 /\ eventuallyp C1)
       -}.
    d_swap; eapply DARewriteIfP; first by d_head.
    simpl_embed.

    d_have {-A
      C1 /\ C2 -> c = c'
     -}.
    {
      d_ifc; d_splitp; d_substp.
      eapply DSCut; first by apply DAPEqualSymmetric.
        d_forallp c; d_forallp c'; simpl_embed.
      by d_splitp; d_clear; d_ifp.
    }
    d_swap; eapply DARewriteIfP; first by d_head.
    simpl_embed.

    d_have {-A
      eventuallyp (c = c') -> c = c'
     -}; first by eapply DSCut; first by eapply DTL133 with (P := {-A c = c' -}).
    d_swap; eapply DARewriteIfP; first by d_head.
    by simpl_embed.
  }

  set A1 := {-A on n, event[0]<- CSLDeliver ' n' ' (c, m) -}.
  set A2 := {-A on n, event[0]<- CSLDeliver ' n' ' (c', m) -}.
  set B1 := {-A on n', event[]-> CPLSend ' n ' m /\ TLeft (Fs' ' n) = c -}.
  set B2 := {-A on n', event[]-> CPLSend ' n ' m /\ TLeft (Fs' ' n) = c' -}.
  d_have {-A
    eventuallyp A2 =>> eventuallyp eventuallyp A2
   -}.
  {
    eapply DSCut; first by apply DTL83_1 with (A := {-A A2 -}).
    by d_splitp.
  }
  eapply DARewriteEntailsP; first by d_rotate 2; d_head.
  eapply DARewriteCongruentPR; first by apply DTL83_1 with (A := {-A B2 -}).
  eapply DARewriteCongruentPR; first by apply DTL83_1 with (A := {-A B2 -}).
  simpl_embed.

  eapply DSCut; first by apply DTL132 with
    (A1 := {-A A1 -})
    (A2 := {-A eventuallyp A2 -})
    (B1 := {-A eventuallyp B1 -})
    (B2 := {-A eventuallyp B2 -}).
  d_ifp; first by d_splitc; d_assumption.
  d_swap; d_clear.
  eapply DARewriteEntailsP; first by d_head.
  simpl_embed.

  d_have {-A
    (A1 /\ eventuallyp A2 =>> c = c') ->
    self (A1 /\ eventuallyp A2 =>> c = c')
   -}; first by eapply DTL129.

  d_swap; eapply DARewriteIfP; first by d_head.
  by simpl_embed.
Admitted.

(* No-duplication
 * If a message is sent at most once, it will be delivered at most once.
 *)
Theorem PL_2 Delta : Context Delta [::] ||- perfect_link, {-A
  forall: forall: forall: (* 2:n, 1:n', 0:m *)
    (on #1, event[]-> CPLSend ' #2 ' #0 =>>
      alwaysp^ ~on #1, event[]-> CPLSend ' #2 ' #0) ->
    (on #2, event[]<- CPLDeliver ' #1 ' #0 =>>
      alwaysp^ ~on #2, event[]<- CPLDeliver ' #1 ' #0)
   -}.
Proof.
  (* Introduce context *)
  set C := perfect_link; rewrite -/C /empty_context.
  d_forallc n Hf_n; d_forallc n' Hf_n';
    d_forallc m Hf_m;
    simpl_embed.
  d_ifc.

  (* By OI' *)
  d_have {-A
    on n, event[]<- CPLDeliver ' n' ' m =>>
    eventuallyp (self-event /\ on n, (CPLDeliver ' n' ' m \in Fois))
   -}.
  {
    d_use DPOI'; d_forallp n; d_forallp {-t CPLDeliver ' n' ' m -};
      simpl_embed.
    eapply DARewriteIfP; first by apply DTL123 with
      (A := {-A self-event /\ on n, (CPLDeliver ' n' ' m \in Fois) -}).
    by simpl_embed.
  }

  (* By InvL *)
  d_have {-A
    self-event /\ on n, (CPLDeliver ' n' ' m \in Fois) =>>
    self-event /\ on n, ((FCount ' (CPLDeliver ' n' ' m) ' Fois) = 1)
   -}.
  {
    eapply DSCut; first by eapply DSEmptyContext; apply DPInvL with
      (A := {-A
          on n, (CPLDeliver ' n' ' m \in Fois) ->
          on n, ((FCount ' (CPLDeliver ' n' ' m)$ Fois) = 1)
         -});
      first by repeat constructor.

    (* request *)
    d_ifp.
      d_forallc e Hf_e; simpl_embed.
      d_ifc; d_splitp; d_swap; d_evalp.

    d_destructp (fun t => {-A (Fs' ' Fn, Fors, Fois) = t -}).
    d_forallp r; d_forallp c; d_splitp; d_swap.
    d_substp; d_evalp.
    d_destructp (fun t => {-A (Fs' ' Fn, Fors, Fois) = t -}).
    d_forallp m. d_forallp n'.
    d_splitp. d_swap.
    d_substp. d_evalp.
    d_ifc. d_swap.
    d_destructtuplep
      {-t Fs' ' Fn -} {-t Fors -} {-t Fois -}
      {-t (FSucc ' c, r) -}
      {-t (CCons ' (CPair ' 0 ' (CSLSend ' n' ' (CPair ' (FSucc ' c) ' m))) ' CNil) -} {-t CNil -}; do 2 d_splitp.
    d_rotate 3. d_substp.
    d_splitp. d_swap.

    eapply DSCut; first by eapply DAPInNil.
    d_forallp {-t (CPLDeliver ' n' ' m) -}.
    eapply DSCut; first by eapply DSNotImpliesFalse with (Ac := {-A (CPLDeliver ' n' ' m) \in CNil -}).
    d_swap; eapply DARewriteIffPL; first by d_head.
    simpl_embed; d_swap; d_clear.
    d_ifp. d_head. d_false.

    (* indication *)
    d_ifp. d_forallc "i". d_forallc e.
    d_ifc. d_splitp. d_swap. d_evalp.
    d_destructp (fun t => {-A (Fs' ' Fn, Fors, Fois) = t -}).
    d_forallp r; d_forallp c; d_splitp; d_swap.
    d_substp; d_evalp.
    d_destructp (fun t => {-A (Fs' ' Fn, Fors, Fois) = t -}).
    d_forallp m; d_forallp c'; d_forallp n'. (* n' or n? *)
    d_splitp. d_swap. d_substp. d_evalp.
    d_destructp (fun t => {-A (Fs' ' Fn, Fors, Fois) = t -}).

    d_orp.
    (* true case *)
    d_splitp. d_swap. d_substp. d_evalp.
    d_destructtuplep
        {-t Fs' ' Fn -} {-t Fors -} {-t Fois -}
        {-t (c, r) -}
        {-t  CNil -} {-t CNil -}; do 2 d_splitp.
    d_ifc. d_substp. d_splitp. d_swap.
    eapply DSCut; first by eapply DAPInNil.
    d_forallp {-t (CPLDeliver ' n' ' m) -}.
    eapply DSCut; first by eapply DSNotImpliesFalse with (Ac := {-A (CPLDeliver ' n' ' m) \in CNil -}).
    d_swap; eapply DARewriteIffPL; first by d_head.
    simpl_embed; d_swap; d_clear.
    d_ifp. d_head. d_false.

    (* false case *)
    d_splitp. d_swap. d_substp. d_evalp.
    d_destructtuplep
      {-t Fs' ' Fn -} {-t Fors -} {-t Fois -}
      {-t (CPair ' c ' (FUnion ' r ' (CCons ' ((n', c)') ' CNil))) -}
      {-t  CNil -} {-t (CCons ' (CPLDeliver ' n' ' m) ' CNil) -}. do 2 d_splitp.
    d_ifc.
    d_splitc. d_splitp. d_head.
    d_subst. d_eval.
    eapply DAPListOcc. by []. by [].

    (* periodics *)
    d_ifp. d_ifc. d_splitp. d_swap. d_evalp.
    d_destructtuplep
      {-t Fs' ' Fn -} {-t Fors -} {-t Fois -}
      {-t Fs ' Fn -}
      {-t  CNil -} {-t CNil -}; do 2 d_splitp.
    d_ifc. d_splitp. d_splitc. d_head.
    d_swap. d_substp.
    eapply DSCut; first by eapply DAPInNil.
    d_forallp {-t (CPLDeliver ' n' ' m) -}.
    eapply DSCut; first by eapply DSNotImpliesFalse with (Ac := {-A (CPLDeliver ' n' ' m) \in CNil -}).
    d_swap; eapply DARewriteIffPL; first by d_head.
    simpl_embed; d_swap; d_clear.
    d_ifp. d_head. d_false.

    eapply DARewriteIffPL; first by apply DSMergeIf with
      (Ap1 := {-A self-event -})
      (Ap2 := {-A on n, CPLDeliver ' n' ' m \in Fois -})
      (Ac := {-A on n, (fun: fun: FCount ' (P 0 0) ' (P 1 0)) ' Fois ' (CPLDeliver ' n' ' m) = 1 -}).
    simpl_embed.

    d_have {-A
              (self-event /\ on n, CPLDeliver ' n' ' m \in Fois =>> self-event /\ on n, (fun: fun: FCount ' (P 0 0) ' (P 1 0)) ' Fois ' (CPLDeliver ' n' ' m) = 1) -}.
    {
      eapply DTGeneralization; first by repeat constructor.
      d_ifc. d_swap. d_splitp. d_swap; d_clear.
      d_ifp. d_head.
      d_splitc. d_swap. d_splitp. d_head. d_head.
    }
    d_head.
  }

  (* by Lemma 96 on (1) and (2) *)
  d_have {-A
            on n, event[]<- CPLDeliver ' n' ' m =>>
                          eventuallyp (self-event /\ on n, ((FOcc ' Fois ' (CPLDeliver ' n' ' m)) = 1)) -}.
  {
    d_rotate 2. d_clear. d_swap.
    eapply DSCut; first by apply DTL96_2 with
                             (A1 := {-A on n, event[]<- CPLDeliver ' n' ' m -})
                             (A2 := {-A self-event /\ on n, (CPLDeliver ' n' ' m \in Fois) -})
                             (A3 := {-A self-event /\ on n, (fun: fun: FCount ' (P 0 0) ' (P 1 0)) ' Fois ' (CPLDeliver ' n' ' m) = 1 -}).
    d_ifp. d_splitc. d_head. d_swap. d_head.
    d_head.
  }

  (* by Lemma 42 *)
  d_have {-A
            self (
                on n, (CPLDeliver ' n' ' m) \in Fois =>>
                                                                   always^ (Fn = n -> (CPLDeliver ' n' ' m) \notin Fois) /\
                                                            alwaysp^ (Fn = n -> (CPLDeliver ' n' ' m) \notin Fois)
         ) -}.
  {
    do 4 d_clear.
    eapply L42.
  }

  (* by SINV on (4) *)
  d_have {-A
            self-event /\ on n, CPLDeliver ' n' ' m \in Fois =>>
                                                                           always^ (self-event /\ Fn = n -> (CPLDeliver ' n' ' m) \notin Fois) /\
                                                                    alwaysp^ (self-event /\ Fn = n -> (CPLDeliver ' n' ' m) \notin Fois) -}.
  {
    eapply DARewriteIfP with (Arp := {-A
                                          (self (on n, CPLDeliver ' n' ' m \in Fois =>>                                                                                          always^ (Fn = n -> CPLDeliver ' n' ' m \notin Fois) /\ alwaysp^ (Fn = n -> CPLDeliver ' n' ' m \notin Fois))) -})
                               (Arc := {-A restrict_assertion {-A self-event -} ( ((on n, CPLDeliver ' n' ' m \in Fois) =>>  (always^ (Fn = n -> CPLDeliver ' n' ' m \notin Fois) /\ alwaysp^ (Fn = n -> CPLDeliver ' n' ' m \notin Fois)))) -}).

    eapply DPSInv_1.
    simpl_embed.
    d_splitp.
    d_swap.
    set A := {-A (self-event -> on n, CPLDeliver ' n' ' m \in Fois) -}.
    set B := {-A always^ (self-event -> Fn = n -> CPLDeliver ' n' ' m \notin Fois) /\
                 alwaysp^ (self-event -> Fn = n -> CPLDeliver ' n' ' m \notin Fois) -}.
    d_have {-A
              always^ (self-event -> on n, CPLDeliver ' n' ' m \in Fois -> B) -> always ((self-event /\ on n, CPLDeliver ' n' ' m \in Fois) -> B) -}.
    {
      d_ifc. d_splitc. d_ifc. d_rotate 3. d_ifp. d_rotate 4. d_splitp. d_swap. d_head. d_head.
      d_have {-A
              (self-event -> on n, CPLDeliver ' n' ' m \in Fois -> B) ->
              ((self-event /\ on n, CPLDeliver ' n' ' m \in Fois) -> B)
              -}.
      {
        d_ifc. d_ifc. d_splitp. d_rotate 2. d_ifp. d_rotate 7. d_head. d_ifp. d_rotate 8. d_head. d_head.

      }

      d_swap. eapply DARewriteIfP; first by d_head. simpl_embed. d_head.
    }
    d_swap.
    eapply DARewriteIfP; first by d_head.
    simpl_embed.
    d_have {-A
              (self-event -> Fn = n -> CPLDeliver ' n' ' m \notin Fois) ->
              ((self-event /\ Fn = n -> CPLDeliver ' n' ' m \notin Fois))
            -}.
    {
      d_ifc. d_ifc. d_splitp. d_rotate 2. d_ifp. d_rotate 7. d_head. d_ifp. d_rotate 8. d_head. d_head.
    }
    d_swap. eapply DARewriteIfP; first by d_head. simpl_embed.
    d_head.
  }

  (* from (3) and (5) *)
  d_have {-A
            on n, event[]<- CPLDeliver ' n' ' m =>>
                          eventuallyp (((FOcc ' Fois ' (CPLDeliver ' n' ' m)) = 1) /\
                                      always^ (self-event /\ Fn = n -> (CPLDeliver ' n' ' m) \notin Fois) /\ alwaysp^ (self-event /\ Fn = n -> (CPLDeliver ' n' ' m) \notin Fois))
          -}.
  {
    d_have {-A ((FOcc ' Fois ' (CPLDeliver ' n' ' m)) = 1) -> CPLDeliver ' n' ' m \in Fois -}.
    {
      d_ifc.
      d_eval.
      eapply DSCut; first by eapply DAPEqualToGE.
      d_forallp {-t FCount ' (CPLDeliver ' n' ' m) ' Fois -}.
      d_forallp 1. d_ifp.
      d_head.
      d_use DAPInOcc.
      d_evalp. d_forallp {-t (CPLDeliver ' n' ' m) -}. d_forallp Fois. d_splitp.
      d_clear. d_ifp. d_head.
      d_head.
    }

    d_have {-A self-event /\ on n, ((FOcc ' Fois ' (CPLDeliver ' n' ' m)) = 1)
               ->
               ((FOcc ' Fois ' (CPLDeliver ' n' ' m)) = 1) /\ (self-event /\ on n, CPLDeliver ' n' ' m \in Fois) -}.
    {
      d_ifc.
      d_splitc. do 2 (d_splitp; d_swap). d_head.
      eapply DARewriteIfP with (Arp := {-A (fun: fun: FCount ' (P 0 0) ' (P 1 0)) ' Fois ' (CPLDeliver ' n' ' m) = 1 -})
                               (Arc := {-A CPLDeliver ' n' ' m \in Fois -}).
      d_head. simpl_embed. d_head.
    }
    eapply DARewriteEntailsP with (Arp := {-A self-event /\ on n, CPLDeliver ' n' ' m \in Fois -})
                                  (Arc := {-A  always^ (self-event /\ Fn = n -> CPLDeliver ' n' ' m \notin Fois) /\
                        alwaysp^ (self-event /\ Fn = n -> CPLDeliver ' n' ' m \notin Fois) -}).
    d_swap. d_head. simpl_embed.
    d_rotate 4.
    eapply DARewriteIfP with (Arp := {-A self-event /\ on n, (fun: fun: FCount ' (P 0 0) ' (P 1 0)) ' Fois ' (CPLDeliver ' n' ' m) = 1 -})
                             (Arc := {-A  (fun: fun: FCount ' (P 0 0) ' (P 1 0)) ' Fois ' (CPLDeliver ' n' ' m) = 1 /\
                        always^ (self-event /\ Fn = n -> CPLDeliver ' n' ' m \notin Fois) /\
                        alwaysp^ (self-event /\ Fn = n -> CPLDeliver ' n' ' m \notin Fois) -}).
    d_rotate 3. d_head. simpl_embed. d_head.
  }

  (* by UNIOI *)
  d_have {-A
            (((FOcc ' Fois ' (CPLDeliver ' n' ' m)) <= 1) /\
             always^ (self-event /\ Fn = n -> (CPLDeliver ' n' ' m) \notin Fois) /\
             alwaysp^ (self-event /\ Fn = n -> (CPLDeliver ' n' ' m) \notin Fois)) =>>
                                                                                             on n, event[]<- CPLDeliver ' n' ' m =>>
                                                                                                          alwaysp^ (~ (on n, event[]<- CPLDeliver ' n' ' m))
          -}.
  {
    d_use DPUniOI.
    d_forallp n. d_forallp Fois. d_forallp {-t CPLDeliver ' n' ' m -}.
    set A := {-A always^ (self-event /\ Fn = n -> (CPLDeliver ' n' ' m) \notin Fois) -}.
    set B := {-A alwaysp^ (self-event /\ Fn = n -> (CPLDeliver ' n' ' m) \notin Fois) -}.
    set D := {-A  (fun: fun: FCount ' (P 0 0) ' (P 1 0)) ' Fois ' (CPLDeliver ' n' ' m) <= 1 -}.
    set E := {-A alwaysp^ (~ (on n, Fd = CNil /\ Fo = OIndication /\ Fe = CPLDeliver ' n' ' m)) -}.
    set F := {-A always^ (~ (on n, Fd = CNil /\ Fo = OIndication /\ Fe = CPLDeliver ' n' ' m)) -}.
    eapply DARewriteIfP with (Arp := {-A E /\ F -})
                             (Arc := {-A E -}).
    d_ifc. d_splitp. d_head.
    simpl_embed.
    d_head.
  }

  (* from (6) and (7) *)
  d_have {-A
            on n, event[]<- CPLDeliver ' n' ' m <~
                          (on n, event[]<- CPLDeliver ' n' ' m =>> alwaysp^ (~ on n, event[]<- CPLDeliver ' n' ' m)) -}.
  {
    d_swap.
    d_use DAPEqualToLe.
    d_forallp {-t (fun: fun: FCount ' (P 0 0) ' (P 1 0)) ' Fois ' (CPLDeliver ' n' ' m) -}. d_forallp 1.
    d_swap.
    eapply DARewriteIfP with (Arp := {-A (fun: fun: FCount ' (P 0 0) ' (P 1 0)) ' Fois ' (CPLDeliver ' n' ' m) = 1 -})
                             (Arc := {-A (fun: fun: FCount ' (P 0 0) ' (P 1 0)) ' Fois ' (CPLDeliver ' n' ' m) <= 1 -}).
    d_head. simpl_embed.
    d_swap. d_clear.
    eapply DARewriteEntailsP with (Arp := {-A (fun: fun: FCount ' (P 0 0) ' (P 1 0)) ' Fois ' (CPLDeliver ' n' ' m) <= 1 /\
                        always^ (self-event /\ Fn = n -> CPLDeliver ' n' ' m \notin Fois) /\
                        alwaysp^ (self-event /\ Fn = n -> CPLDeliver ' n' ' m \notin Fois) -})
                                  (Arc := {-A on n, event[]<- CPLDeliver ' n' ' m =>> alwaysp^ (~ on n, event[]<- CPLDeliver ' n' ' m) -}).
    d_head. simpl_embed.
    d_head.
  }

  d_have {-A
            on n, event[]<- CPLDeliver ' n' ' m =>>
                          alwaysp^ (~ (on n, event[]<- CPLDeliver ' n' ' m)) -}.
  {
    set A := {-A  on n, event[]<- CPLDeliver ' n' ' m -}.

    eapply DARewriteEntailsP with (Arp := {-A eventuallyp always (A -> alwaysp^ (~A)) -})
                                  (Arc := {-A (A -> alwaysp^ (~A)) -}).
    eapply DTL98_1.
    simpl_embed.
    d_subst.
    set B := {-A on n, Fd = CNil /\ Fo = OIndication /\ Fe = CPLDeliver ' n' ' m -}.
    d_have {-A
              (B -> (B -> alwaysp^ (~ B))) -> (B -> alwaysp^ (~ B)) -}.
    {
      d_ifc. d_ifc. d_swap. d_ifp. d_head. d_ifp. d_head. d_head.
    }
    d_swap. eapply DARewriteIfP with (Arp := {-A (B -> B -> alwaysp^ (~ B)) -})
                                     (Arc := {-A  B -> alwaysp^ (~ B) -}).
    d_head.
    simpl_embed.
    d_head.
  }
  d_head.
Qed.

(* No-forge
 * If a node n delivers a message m with sender n', then m was previously sent
 * to n by node n'.
 *)
Theorem PL_3 Delta : Context Delta [::] ||- perfect_link, {-A
  on n, event[]<- CPLDeliver ' n' ' m <~
  on n', event[]-> CPLSend ' n ' m
 -}.
Proof.
  (* By OI' *)
  d_have {-A
    on n, event[]<- CPLDeliver ' n' ' m =>>
    eventuallyp^ (self-event /\ on n,
      (CPLDeliver ' n' ' m \in Fois))
   -}.
  {
    (* Instantiate OI' *)
    by d_use DPOI'; d_forallp n; d_forallp {-t CPLDeliver ' n' ' m -}.
  }

  (* By InvL *)
  d_have {-A
    self-event /\ on n, (CPLDeliver ' n' ' m \in Fois) =>>
    exists: c: on n, event[0]<- CSLDeliver ' n' ' (c, m)
   -}.
  {
    d_clear. (* Clean up the context *)

    (* Instantiate InvL *)
    eapply DSCut; first by apply DPInvL with
      (A := {-A
          on n, (CPLDeliver ' n' ' m \in Fois) ->
          exists: c: on n, event[0]<- CSLDeliver ' n' ' (c, m)
         -}); first by repeat constructor.

    (* Prove for requests *)
    d_ifp.
    d_forallc e.
    d_ifc; d_splitp; d_swap; d_evalp.
    d_destructp (fun t => {-A (Fs' ' Fn, Fors, Fois) = t -}).
    d_forallp {-t (c, m) -}; d_forallp n'; d_splitp; d_swap.
    d_substp; d_evalp.
    d_destructp (fun t => {-A (Fs' ' Fn, Fors, Fois) = t -}).
    d_forallp {-t (c, m) -}.
    d_forallp n'; d_splitp; d_swap.
    d_substp; d_evalp.
    d_ifc; d_swap.
    d_destructtuplep
      {-t Fs' ' Fn -} {-t Fors -} {-t Fois -}
        {-t (FSucc ' n', (c, m)) -}
        {-t (CCons ' (CPair ' 0 ' (CSLSend ' n' ' (CPair ' (FSucc ' n') ' (c, m)))) ' CNil) -} {-t CNil -}; do 2 d_splitp.
    d_rotate 3; d_substp; d_splitp; d_swap.

    eapply DSCut; first by eapply DAPInNil.
    d_forallp {-t CPLDeliver ' n' ' m -}.
    eapply DSCut; first by eapply DSNotImpliesFalse with (Ac := {-A
                                                                   CPLDeliver ' n' ' m \in CNil -}).
    d_swap; eapply DARewriteIffPL; first by d_head.
    simpl_embed; d_swap; d_clear.
      by d_ifp; first by d_head; d_false.

    (* Prove for indications *)
      d_ifp.
      d_forallc "i"; d_forallc e.
      d_ifc. d_splitp. d_swap. d_evalp.
      d_destructp (fun t => {-A (Fs' ' Fn, Fors, Fois) = t -}).
      d_forallp m; d_forallp n'; d_splitp; d_swap.
      d_substp; d_evalp.
      d_destructp (fun t => {-A (Fs' ' Fn, Fors, Fois) = t -}).
      d_forallp m; d_forallp c; d_forallp n'.
      d_splitp; d_swap.
      d_substp; d_evalp.
      d_destructp (fun t => {-A (Fs' ' Fn, Fors, Fois) = t -}).

      d_orp.
      (* true case *)
      d_splitp; d_swap. d_substp. d_evalp.
      d_destructtuplep
        {-t Fs' ' Fn -} {-t Fors -} {-t Fois -}
        {-t (n', m) -}
        {-t  CNil -} {-t CNil -}; do 2 d_splitp.
      d_ifc. d_substp; d_splitp; d_swap.
      eapply DSCut; first by eapply DAPInNil.
      d_forallp {-t CPLDeliver ' n' ' m -}.
      eapply DSCut; first by eapply DSNotImpliesFalse with (Ac := {-A
                                                                     CPLDeliver ' n' ' m \in CNil -}).
      d_swap; eapply DARewriteIffPL; first by d_head.
      simpl_embed; d_swap; d_clear.
        by d_ifp; first by d_head; d_false.

      (* false case *)
      d_splitp; d_swap. d_substp. d_evalp.
      d_destructtuplep
        {-t Fs' ' Fn -} {-t Fors -} {-t Fois -}
        {-t (n', (FUnion ' m ' (CCons ' (n', c) ' CNil))) -}
        {-t  CNil -} {-t (CCons ' (CPLDeliver ' n' ' m) ' CNil) -}; do 2 d_splitp.

      d_ifc. d_splitp.
      d_existsc c.
      d_rotate 6.
      d_destructpairp {-t "i" -} {-t e -} {-t 0 -} {-t (CSLDeliver ' n' ' (c, m)) -}.
      simpl_embed; d_splitp.

      d_splitc. d_rotate 4. d_head.
      d_splitc. d_rotate 3. d_substp. d_splitp. d_head.
      d_rotate 3. do 2 (d_splitp; d_swap). d_swap. d_splitc. d_head.
      d_swap. d_substp. d_head.

    (* Prove for periodics *)
    d_ifp.
    d_ifc. d_splitp. d_swap. d_evalp.
    d_destructtuplep
      {-t Fs' ' Fn -} {-t Fors -} {-t Fois -}
      {-t Fs ' Fn -}
      {-t  CNil -} {-t CNil -}; do 2 d_splitp.
    d_ifc. d_substp. d_splitp; d_swap.
    eapply DSCut; first by eapply DAPInNil.
    d_forallp {-t CPLDeliver ' n' ' m -}.
    eapply DSCut; first by eapply DSNotImpliesFalse with (Ac := {-A
                                                                   CPLDeliver ' n' ' m \in CNil -}).

    d_swap; eapply DARewriteIffPL; first by d_head.
    simpl_embed; d_swap; d_clear.
      by d_ifp; first by d_head; d_false.

    by eapply DARewriteIffPL; first by apply DSMergeIf with
      (Ap1 := {-A self-event -})
      (Ap2 := {-A on n, (CPLDeliver ' n' ' m \in Fois) -})
      (Ac := {-A exists: c:
        on n, event[0]<- CSLDeliver ' n' ' (c, m) -}).
  }

  (* By Lemma 96 on (1) and (2) *)
  d_have {-A
    on n, event[]<- CPLDeliver ' n' ' m <~
    exists: c: on n, event[0]<- CSLDeliver ' n' ' (c, m)
   -}.
  {
    eapply DSCut;
    first by eapply DTL96_2 with (A1 := {-A
                                  on n, event[]<- CPLDeliver ' n' ' m -})
                        (A2 := {-A
                                  (self-event /\ on n, (CPLDeliver ' n' ' m \in Fois)) -})
                        (A3 := {-A
                                  exists: c : on n, event[0]<- CSLDeliver ' n' ' (c, m) -}).
    d_ifp.
    d_splitc.
    d_swap.
    eapply DARewriteIfP. by apply DTL123 with (A := {-A
                                                       (self-event /\ on n, (CPLDeliver ' n' ' m \in Fois)) -}).
    simpl_embed.
    d_head. d_head. d_head.
  }

  (* By OR' *)
  d_have {-A
    forall: c:
    on n', event[0]-> CSLSend ' n ' (c, m) =>>
    eventuallyp (self-event /\
      on n', ((0, CSLSend ' n ' (c, m)) \in Fors))
   -}.
  {
    d_forallc c.

    d_use DPOR'.
      d_forallp n'; d_forallp 0; d_forallp {-t CSLSend ' n ' (c, m) -}.
      (*
      d_have {-A
                 eventuallyp^ (self-event /\
                               Fn = n' /\ CPair ' 0 ' (CSLSend ' n ' (c, m)) \in Fors) =>>
                                                                                                             eventuallyp (self-event /\
                                                                                                                          Fn = n' /\ CPair ' 0 ' (CSLSend ' n ' (c, m)) \in Fors) -}.
      {
        d_splitc.
        eapply DTL123.
       *)
    d_have {-A (Fn = n' /\ Fd = [0] /\ Fo = ORequest /\ Fe = CSLSend ' n ' (c, m) =>>
                                                                                            eventuallyp (self-event /\ Fn = n' /\ CPair ' 0 ' (CSLSend ' n ' (c, m)) \in Fors)) -}.
    {
      d_splitc.
      d_splitp; d_swap; d_clear.
      eapply DARewriteIfP with (Arp := {-A eventuallyp^ (self-event /\
                                                         Fn = n' /\ CPair ' 0 ' (CSLSend ' n ' (c, m)) \in Fors) -})
                               (Arc := {-A eventuallyp (self-event /\
                                                        Fn = n' /\ CPair ' 0 ' (CSLSend ' n ' (c, m)) \in Fors) -}).
      eapply DTL123.
      simpl_embed.
      d_head.
      d_splitp; d_clear.
      eapply DARewriteIfP with (Arp := {-A eventuallyp^ (self-event /\
                                                         Fn = n' /\ CPair ' 0 ' (CSLSend ' n ' (c, m)) \in Fors) -})
                               (Arc := {-A eventuallyp (self-event /\
                                                        Fn = n' /\ CPair ' 0 ' (CSLSend ' n ' (c, m)) \in Fors) -}).
      eapply DTL123.
      simpl_embed.
      d_head.
    }
    d_head.
  }

  (* By InvL *)
  d_have {-A
    forall: c:
    self-event /\ on n', ((0, CSLSend ' n ' (c, m)) \in Fors) =>>
    on n', event[]-> CPLSend ' n ' (m)
   -}.
  {
    do 4 d_clear. (* Clean up the context *)

    (* Instantiate InvL *)
    eapply DSCut; first by apply DPInvL with
                      (A := {-A
                               on n', ((0, CSLSend ' n ' (c, m)) \in Fors) ->
                                                                                     on n', event[]-> CPLSend ' n ' (m)
                       -}); first by repeat constructor.

    (* Prove for requests *)
    d_ifp.
    d_forallc e.
    d_ifc; d_splitp; d_swap. d_evalp.
    d_destructp (fun t => {-A (Fs' ' Fn, Fors, Fois) = t -}).
    d_forallp r; d_forallp c.
    d_splitp; d_swap. d_substp. d_evalp.
    d_destructp (fun t => {-A (Fs' ' Fn, Fors, Fois) = t -}).
    d_forallp {-t (m) -}; d_forallp n.
    d_splitp; d_swap.
    d_substp; d_evalp.
    d_destructtuplep
      {-t Fs' ' Fn -} {-t Fors -} {-t Fois -}
      {-t (FSucc ' c, r) -}
      {-t (CCons ' (CPair ' 0 ' (CSLSend ' n ' (CPair ' (FSucc ' c) ' (m)))) ' CNil) -} {-t CNil -}; do 2 d_splitp.
    d_ifc; d_splitp.
    d_splitc; first by d_head.
    d_rotate 7. do 2 (d_splitp; d_swap).
    d_splitc. do 2 d_rotate. d_head.
    d_splitc; d_swap; first by d_head.
    d_swap; d_substp; first by d_head.

    (* Prove for indications *)
    d_ifp.
    d_forallc "i"; d_forallc e.
    d_ifc.
    d_splitp; d_swap; d_substp; d_evalp.
    d_destructp (fun t => {-A (Fs' ' Fn, Fors, Fois) = t -}).
    d_forallp r; d_forallp c.
    d_splitp; d_swap. d_substp. d_evalp.
    d_destructp (fun t => {-A (Fs' ' Fn, Fors, Fois) = t -}).
    d_forallp m. d_forallp c'. d_forallp n.
    d_splitp; d_swap.
    d_substp. d_evalp.
    d_destructp (fun t => {-A (Fs' ' Fn, Fors, Fois) = t -}).

    d_orp.
    (* true case *)
    d_splitp; d_swap.
    d_substp; d_evalp.
    d_destructtuplep
        {-t Fs' ' Fn -} {-t Fors -} {-t Fois -}
        {-t (c, r) -}
        {-t  CNil -} {-t CNil -}; do 2 d_splitp.
    d_ifc.
    d_subst.
    d_splitp; d_swap.
    eapply DSCut; first by eapply DAPInNil.
    d_forallp {-t CPair ' 0 ' (CSLSend ' n ' (c, m)) -}.
    eapply DSCut; first by eapply DSNotImpliesFalse with (Ac := {-A
                                                                   CPair ' 0 ' (CSLSend ' n ' (c, m)) \in CNil -}).
    d_swap; eapply DARewriteIffPL; first by d_head.
    simpl_embed; d_swap; d_clear.
      by d_ifp; first by d_head; d_false.

    (* false case *)
    d_splitp; d_swap.
    d_substp; d_evalp.
    d_destructtuplep
      {-t Fs' ' Fn -} {-t Fors -} {-t Fois -}
      {-t (CPair ' c ' (FUnion ' r ' (CCons ' ((n, c)') ' CNil))) -}
      {-t  CNil -} {-t (CCons ' (CPLDeliver ' n ' m) ' CNil) -}; do 2 d_splitp.
    d_ifc; d_splitp; d_swap.
    d_substp.
    eapply DSCut; first by eapply DAPInNil.
    d_forallp {-t CPair ' 0 ' (CSLSend ' n ' (c, m)) -}.
    eapply DSCut; first by eapply DSNotImpliesFalse with (Ac := {-A
                                                                   CPair ' 0 ' (CSLSend ' n ' (c, m)) \in CNil -}).
    d_swap; eapply DARewriteIffPL; first by d_head.
    simpl_embed; d_swap; d_clear.
      by d_ifp; first by d_head; d_false.

    (* Prove for peridoics *)
    d_ifp.
    d_ifc. d_splitp. d_swap. d_evalp.
    d_destructtuplep
      {-t Fs' ' Fn -} {-t Fors -} {-t Fois -}
      {-t Fs ' Fn -}
      {-t  CNil -} {-t CNil -}; do 2 d_splitp.
    d_ifc; d_substp.
    d_splitp; d_swap.
    eapply DSCut; first by eapply DAPInNil.
    d_forallp {-t CPair ' 0 ' (CSLSend ' n ' (c, m)) -}.
    eapply DSCut; first by eapply DSNotImpliesFalse with (Ac := {-A
                                                                   CPair ' 0 ' (CSLSend ' n ' (c, m)) \in CNil -}).
    d_swap; eapply DARewriteIffPL; first by d_head.
    simpl_embed; d_swap; d_clear.
      by d_ifp; first by d_head; d_false.

    eapply DARewriteIffPL; first by apply DSMergeIf with
      (Ap1 := {-A self-event -})
      (Ap2 := {-A on n', (CPair ' 0 ' (CSLSend ' n ' (c, m)) \in Fors) -})
      (Ac := {-A on n', event[]-> CPLSend ' n ' (m) -}).
    simpl_embed.
    d_forallc c; d_head.
  }

  (* By Lemma 96 on (4) and (5) *)
  d_have {-A
    forall: c:
    on n', event[0]-> CSLSend ' n ' (c, m) <~
    on n', event[]-> CPLSend ' n ' m
   -}.
  {

    d_forallc c.
    eapply DSCut;
      first by eapply DTL96_2 with
          (A1 := {-A
                    on n', event[0]-> CSLSend ' n ' (c, m) -})
          (A2 := {-A
                    self-event /\ on n', (CPair ' 0 ' (CSLSend ' n ' (c, m)) \in Fors) -})
          (A3 := {-A
                    on n', event[]-> CPLSend ' n ' (m) -}).
    d_ifp.
    d_splitc.
    d_swap.
    d_forallp c. d_head.
    d_forallp c. d_head.
    d_head.
  }

  (* By PL_SL_2 *)
  d_have {-A
    exists: c:
    on n, event[0]<- CSLDeliver ' n' ' (c, m) <~
    on n', event[0]-> CSLSend ' n ' (c, m)
   -}.
  {
    do 6 d_clear. (* Clean up the context *)
    d_have (derives_assertion PL_SL_2); first by
      d_clearv n; d_clearv n'; d_clearv m;
      apply PL_SL_2.
    by d_existsc c;
      d_forallp n; d_forallp n'; d_forallp {-t (c, m) -}.
  }

  (* From Lemma 85 on (3), PL_SL_2, and (6) *)
  d_have {-A
            exists: c: on n, event[]<- CPLDeliver ' n' ' m <~
                          on n', event[0]-> CSLSend ' n ' (c, m)
          -}.
  d_existsc c.
  eapply DTL85 with
             (A1 := {-A on n, event[]<- CPLDeliver ' n' ' m -})
             (A2 := {-A on n, event[0]<- CSLDeliver ' n' ' (c, m) -})
             (A3 := {-A on n', event[0]-> CSLSend ' n ' (c, m) -}).
  - d_rotate 4.
    d_have {-A
              (exists: c : on n, event[0]<- CSLDeliver ' n' ' (c, m)) =>>
                                           on n, event[0]<- CSLDeliver ' n' ' (c, m) -}.
    eapply DTGeneralization; first by repeat constructor.
    d_ifc. d_existsp c. d_head.
    d_swap.
    eapply DARewriteEntailsP with (Arp := {-A exists: c : on n, event[0]<- CSLDeliver ' n' ' (c, m) -})
                                  (Arc := {-A on n, event[0]<- CSLDeliver ' n' ' (c, m) -}).
    d_head.
    simpl_embed.
    d_head.
  -
    d_existsp c.
    d_head.

  d_have {-A
            on n, event[]<- CPLDeliver ' n' ' m <~
                          on n', event[]-> CPLSend ' n ' m -}.
  d_existsp c.
  eapply DTL85.
  - by [].
  - d_rotate 2.
    d_forallp c.
    d_head.
  d_head.
Qed.
