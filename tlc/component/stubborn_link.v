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

  dforallc n; dforallc n'; dforallc m; dsimplfresh.
  difc; dsplitp.

  (* By IR *)
  dhave {-A
    on n, event[]-> CSLSend ' n' ' m =>>
    self-event /\ (n', m) \in (Fs' ' n)
  -}.
  {
    (* Instantiate IR *)
    duse DPIR; dforallp {-t CSLSend ' n' ' m -}; dsimplp.

    ddestructpairp.

    dhave {-A
      on n, event[]-> CSLSend ' n' ' m =>>
      event[]-> CSLSend ' n' ' m
    -}.
    {
      by dtgen; difc; dsplitp; dassumption.
    -}
    dttrans; dclear.

    dhave {-A
      (Fs' ' Fn = Fs ' Fn \union [(n', m)] /\
      Fors = [(0, CFLSend ' n' ' m)]) /\ Fois = [] =>>
      (n', m) \in Fs' ' Fn
    -}.
    {
      dt_gen.
      difc; dsplitp; dsplitp; dsubstc.
      eapply DSCut; first by eapply DAPInUnion.
      dforallp {-t Fs ' Fn -};
        dforallp {-t [(n', m)] -};
        dforallp {-t (n', m) -};
        simpl_embed;
        dsplitp; dswap; dclear; difp.
      dright; eapply DAPIn; first by []; last by rewrite mem_seq1.
      by dhead.
    -}

    dswap; dt_trans; dclear.
    dswap; eapply DARewriteIfP; first by dhead.
    simpl_embed.

    eapply DSCut; first by apply DSIfAndSplit with
      (Ap := {-A event[]-> CSLSend ' n' ' m -})
      (Acl := {-A self-event -})
      (Acr := {-A (n', m) \in Fs' ' Fn -}).
    dsplitp; dswap; dclear; difp.
      dsplitc; last by dsplitp.
      duse_empty DPTopRequestSelf.
      by dforallp {-t CSLSend ' n' ' m -}; dsplitp.

    do 4 (dswap; dclear). (* Clean up the context *)
    dhave {-A on n, event[]-> CSLSend ' n' ' m -> self-event /\
      (n', m) \in Fs' ' n -}.
      difc; dsplitp; drotate 2.
      difp; first by dswap.
      by dsubstp.

    dhave {-A on n, event[]-> CSLSend ' n' ' m =>> self-event /\
      (n', m) \in Fs' ' n -}.
    apply DTGeneralization; first by repeat constructor.
    dhead. dhead.
  -}

  (* By InvS'' *)
  dhave {-A
    self-event /\ (n', m) \in (Fs' ' n) =>>
    always^ (self-event -> (n', m) \in (Fs ' n))
  -}.
  {
    (* Instantiate InvS'' *)
    set S := {-A forall: (* 0:ts *) (n', m) \in $$0 -}.
    eapply DSCut. repeat dclear; apply DPInvS'' with (S0 := S);
      [by auto_is_closed | by repeat econstructor].
    dforallp n; simpl_embed.

    (* Prove property for requests *)
    difp.
      dforallc s Hf_s; dforallc e Hf_e;
        difc; dapply.
      eapply DARewriteIffPL; first by
        duse DAPConcatIn; dforallp {-t (n', m) -}; dforallp s; dhead.
      simpl_embed.

      dexistsp sl Hf_sl; dexistsp sr Hf_sr; simpl_embed.
      dsubstc; distinguish_variables.
      devalc.
      ddestructc (fun t => {-A (n', m) \in
        match: t with: {($, $, $) -> $$0} -}); rewrite /=.
      dforallc m'' Hf_m''; dforallc n'' Hf_n''; simpl_embed.
      difc; dsubstc; distinguish_variables; devalc.

      duse DAPInUnion.
      dforallp {-t sl ++ [(n', m)] ++ sr -};
        dforallp {-t [(n'', m'')] -};
        dforallp {-t (n', m) -}; simpl_embed.
      dsplitp; dswap; dclear; difp.
        dleft.
        duse DAPInConcat.
        dforallp sl;
          dforallp {-t [(n', m)] ++ sr -};
          dforallp {-t (n', m) -}; simpl_embed.
        difp.
          dright.
          duse DAPInConcat.
          dforallp {-t [(n', m)] -};
            dforallp sr;
            dforallp {-t (n', m) -}; simpl_embed.
          difp; first by dleft; eapply DAPIn; first by []; last by rewrite mem_seq1.
          dhead.
        dhead.

      dhead.

    (* Prove property for indications *)
    difp.
      dforallc s Hf_s; dforallc i Hf_i; dforallc e Hf_e;
        difc; dapply.

      devalc.
      ddestructc (fun t => {-A (n', m) \in
        match: t with: {($, $, $) -> $$0} -}); rewrite /=.
      dforallc m'' Hf_m''; dforallc n'' Hf_n''; simpl_embed.
      difc; dsubstc; distinguish_variables.
      by devalc; dclear.

    (* Prove property for periodics *)
    difp.
      by dforallc s Hf_s; difc; devalc; dapplyp.

    by devalp.
  -}

  (* From (2) and (3) *)
  dhave {-A
    on n, event[]-> CSLSend ' n' ' m =>>
    always^ (self-event -> (n', m) \in (Fs ' n))
  -}.
  {
    drotate 1; eapply DARewriteEntailsP; first by drotate 2.
    simpl_embed.
    by dt_trans; dassumption.
  -}

  (* By APerSA *)
  dhave {-A
    correct n -> (self-event -> (n', m) \in (Fs ' n)) =>>
    always eventually on n,
      (self-event /\ (0, CFLSend ' n' ' m) \in Fors)
  -}.
  {
    difc; dclear.

    (* Instantiate APerSA *)
    set S := {-A forall: (* 0:ts *) (n', m) \in $$0 -}.
    set A := {-A on n,
      (self-event /\ (0, CFLSend ' n' ' m) \in Fors) -}.
    eapply DSCut. repeat dclear; apply DPAPerSA with (S := S) (A := A);
      [by auto_is_closed | by repeat econstructor | by repeat econstructor].
    dforallp n; devalp; simpl_embed.

    difp.
      difc; do 3 (dsplitp; dswap).
      devalp.
      set tf := {-t fun:
          match: $$0 with:
          { ($, $) -> (0, CFLSend ' $$0 ' $$1) }
        -};
        ddestructpairp; do 2 dsplitp.

      dsplitc; first by dassumption.
      dsplitc; first by dassumption.
      dswap; dsubstc.
      duse DAPInMap.
      dforallp tf; dforallp {-t (n', m) -};
        dforallp {-t Fs ' n -};
        simpl_embed.
      dsplitp; dswap; dclear; difp; first by dassumption.
      by devalp.

    difp; first by dassumption.
    by devalp.
  -}

  (* From (4) and (5) *)
  dhave {-A
    on n, event[]-> CSLSend ' n' ' m =>>
    always^ eventually on n,
      (self-event /\ (0, CFLSend ' n' ' m) \in Fors)
  -}.
  {
    difp; first by dassumption.
    drotate 1; eapply DARewriteEntailsP; first by drotate 4; dhead.
    simpl_embed.
    eapply DARewriteCongruentCR; first by apply DTL119 with (A := {-A
      eventually on n,
        (self-event /\ (0, CFLSend ' n' ' m) \in Fors)
      -}).
    by simpl_embed.
  -}

  (* From OR *)
  (* NOTE: sendfl(n, m) should be sendfl(n', m) *)
  dhave {-A
    on n, (self-event /\ (0, CFLSend ' n' ' m) \in Fors) =>>
    eventually^ on n, event[0]-> CFLSend ' n' ' m
  -}.
  {
    (* Instantiate OR *)
    by duse DPOR;
      dforallp n; dforallp 0; dforallp {-t CFLSend ' n' ' m -}.
  -}

  (* From (6) and (7) *)
  (* NOTE: sendfl(n, m) should be sendfl(n', m) *)
  dhave {-A
    on n, event[]-> CSLSend ' n' ' m =>>
    always^ eventually eventually^ on n, event[0]-> CFLSend ' n' ' m
  -}.
  {
    drotate 1; eapply DARewriteEntailsP;
      first by drotate 6; dhead.
    by simpl_embed; rewrite andbF.
  -}

  (* From lemma 120 on (8) *)
  (* NOTE: Lemma 84 does not apply here; must use new lemma 120 instead *)
  dhave {-A
    on n, event[]-> CSLSend ' n' ' m =>>
      always^ eventually^ on n, event[0]-> CFLSend ' n' ' m
  -}.
  {
    eapply DARewriteEntailsP; first by apply DTL120_3 with (A := {-A
      on n, event[0]-> CFLSend ' n' ' m -}).
    by simpl_embed.
  -}

  (* By rule FLoss on (1) and (9) *)
  dhave {-A
    on n, event[]-> CSLSend ' n' ' m =>>
    always^ eventually^ on n', event[0]<- CFLDeliver ' n ' m
  -}.
  {
    (* Instantiate FLoss *)
    duse DPFLoss.
    dforallp n; dforallp n'; dforallp m; dforallp 0.
    difp; first by dassumption.

    drotate 1; eapply DARewriteIfP;
      first by by drotate 9; dhead.
    by simpl_embed.
  -}

  (* From rule IIOI *)
  dhave {-A
    on n', event[0]<- CFLDeliver ' n ' m =>>
    eventually^ on n', event[]<- CSLDeliver ' n ' m
  -}.
  {
    (* Instantiate IIOI *)
    eapply DSCut. repeat dclear; eapply DPIIOI with (S0 := {-A forall: ATrue -});
      [by auto_is_closed | by repeat econstructor].
    dforallp n'; dforallp 0; dforallp {-t CFLDeliver ' n ' m -};
      dforallp {-t CSLDeliver ' n ' m -}; simpl_embed.
    difp.
      dforallc s Hf_s; simpl_embed; dsplitc; first by dapplyc; dnotc.
      by devalc.
    devalp.

    eapply DARewriteIffCR; first by eapply DSAndElimination with (A :=
      {-A on n', event[0]<- CFLDeliver ' n ' m -}).
    by simpl_embed; rewrite andbF.
  -}

  (* From (10) and (11) *)
  dhave {-A
    on n, event[]-> CSLSend ' n' ' m =>>
    always^ eventually^ eventually^
      on n', event[]<- CSLDeliver ' n ' m
  -}.
  {
    drotate 1; eapply DARewriteEntailsP;
      first by drotate 10; dhead.
    by simpl_embed; rewrite andbF.
  -}

  (* From lemma 84 and (12) *)
  (* NOTE: Lemma 84 does not apply here; must use new lemma 120 instead *)
  dhave {-A
    on n, event[]-> CSLSend ' n' ' m =>>
    always^ eventually^
      on n', event[]<- CSLDeliver ' n ' m
  -}.
  {
    eapply DARewriteEntailsP; first by apply DTL120_2 with (A := {-A
      on n', event[]<- CSLDeliver ' n ' m -}).
    by simpl_embed.
  -}

  eapply DARewriteIfP; first by apply DTL121 with (A := {-A
    on n', event[]<- CSLDeliver ' n ' m -}).
  simpl_embed.
  eapply DARewriteIfP; first by apply DTL122 with (A := {-A
    on n', event[]<- CSLDeliver ' n ' m -}).
  by simpl_embed.
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
  dforallc n Hf_n; dforallc n' Hf_n'; dforallc m Hf_m; simpl_embed.

  (* By OI' *)
  dhave {-A
    on n, event[]<- CSLDeliver ' n' ' m =>>
    eventuallyp (self-event /\ on n, (CSLDeliver ' n' ' m \in Fois))
  -}.
  {
    (* Instantiate OI' *)
    duse DPOI'; dforallp n; dforallp {-t CSLDeliver ' n' ' m -}; simpl_embed.

    eapply DARewriteIfP; first by apply DTL123 with (A := {-A
      self-event /\ on n, (CSLDeliver ' n' ' m \in Fois) -}).
    by simpl_embed.
  -}

  (* By InvL *)
  dhave {-A
    self-event /\ on n, (CSLDeliver ' n' ' m \in Fois) =>>
    on n, event[0]<- CFLDeliver ' n' ' m
  -}.
  {
    dclear. (* Clean up the context *)

    (* Instantiate InvL *)
    eapply DSCut; first by apply DSEmptyContext; apply DPInvL with (A := {-A
        on n, (CSLDeliver ' n' ' m \in Fois) ->
        on n, event[0]<- CFLDeliver ' n' ' m
      -}); first by repeat constructor.

    (* Prove for requests *)
    difp.
      (* Obtain the first contradictory premise *)
      dforallc e Hf_e; simpl_embed.
      difc; dsplitp; dswap; devalp.
      ddestructp (fun t => {-A (Fs' ' Fn, Fors, Fois) = t -});
        dexistsp m_ Hf_m_; dexistsp n'_ Hf_n'_; dsplitp; dswap;
        dsubstp; devalp.
      ddestructpairp; do 2 dsplitp.
      do 2 dclear; do 2 (dswap; dclear). (* Clean up the context *)

      (* Obtain the second contradictory premise *)
      by difc; dsplitp; dclear; dsubstp; devalp.


    (* Prove for indications *)
    difp.
      dforallc i Hf_i; dforallc e Hf_e; simpl_embed.
      difc; dsplitp; dswap; devalp.
      ddestructp (fun t => {-A (Fs' ' Fn, Fors, Fois) = t -});
        dexistsp m_ Hf_m_; dexistsp n'_ Hf_n'_; dsplitp; dswap;
        dsubst; devalp.
      ddestructpairp; do 2 dsplitp.
      difc; dsplitp.
      dsplitc; first by dhead.
      dswap; do 3 (dswap; drotate 1); dsubstp.
      din_cons_pl; simpl_embed.
      dorp; last by devalp.
      eapply DSEqualEvent; dsplitp.
      dsubstc; dclear; dsubstc; dclear;
        distinguish_variables; rewrite eq_refl.
      dclear; ddestructpairp; dsplitp; drotate 2; do 3 (dswap; dclear).
      by do 2 (dsubstp; dswap; dclear);
        distinguish_variables; rewrite eq_refl.

    (* Prove for periodics *)
    difp.
      (* Obtain the first contradictory premise *)
      difc; dsplitp; dswap; devalp.
      ddestructpairp; repeat dsplitp.
      do 2 dclear; (dswap; dclear). (* Clean up the context *)

      (* Obtain the second contradictory premise *)
      by difc; dsplitp; dclear; dsubstp; devalp.

    eapply DARewriteIffPL; first by apply DSMergeIf with
      (Ap1 := {-A self-event -})
      (Ap2 := {-A on n, (CSLDeliver ' n' ' m \in Fois) -})
      (Ac := {-A on n, event[0]<- CFLDeliver ' n' ' m -}).
    by simpl_embed.
  -}

  (* From (1) and (2) *)
  dhave {-A
    on n, event[]<- CSLDeliver ' n' ' m <~
    on n, event[0]<- CFLDeliver ' n' ' m
  -}.
  {
    drotate 1; eapply DARewriteEntailsP; first by dhead.
    by simpl_embed.
  -}

  (* By NForge *)
  dhave {-A
    on n, event[0]<- CFLDeliver ' n' ' m <~
    on n', event[0]-> CFLSend ' n ' m
  -}.
  {
    (* Instantiate NForge *)
    by duse DPNForge;
      dforallp n'; dforallp n; dforallp m; dforallp 0.
  -}

  (* By lemma 85 on (3) and (4) *)
  dhave {-A
    on n, event[]<- CSLDeliver ' n' ' m <~
    on n', event[0]-> CFLSend ' n ' m
  -}.
  {
    by eapply DTL85; first by drotate 1; dhead.
  -}

  (* By OR' *)
  dhave {-A
    on n', event[0]-> CFLSend ' n ' m =>>
    eventuallyp (self-event /\ on n',
      ((0, CFLSend ' n ' m) \in Fors))
  -}.
  {
    (* Instantiate OR' *)
    duse DPOR';
      dforallp n'; dforallp 0; dforallp {-t CFLSend ' n ' m -}; simpl_embed.

    eapply DARewriteIfP; first by apply DTL123 with (A := {-A
      self-event /\ on n', ((0, CFLSend ' n ' m) \in Fors) -}).
    by simpl_embed.
  -}

  (* By InvSA *)
  dhave {-A
    self-event /\ on n', ((n, m) \in Fs ' n') =>>
    eventuallyp^ on n', event[]-> CSLSend ' n ' m
  -}.
  {
    do 6 dclear. (* Clean up the context *)

    (* Instantiate InvSA *)
    eapply DSCut; first by apply DPInvSA with
      (S0 := {-A forall: (* 0:ts *) on n', ((n, m) \in $$0) -})
      (A := {-A event[]-> CSLSend ' n ' m -});
      [by auto_is_closed | by repeat econstructor | by repeat econstructor].
    dforallp n'; simpl_embed.

    (* Prove for initialization *)
    difp.
      devalc.
      by dnotc; dsplitp; dassumption.

    (* Prove for requests *)
    difp.
      dforallc e Hf_e; devalc.
      difc; dsplitp; dsplitp; do 2 (dswap; dsplitp).
      dsplitc; first by dassumption.
      dsplitc; first by dassumption.
      drotate 4; dsplitp.
      ddestructp (fun t => {-A (Fs' ' Fn, Fors, Fois) = t -});
        dexistsp m_ Hf_m_; dexistsp n_ Hf_n_; dsplitp;
        dswap; dsubstp; devalp;
        ddestructpairp; repeat dsplitp.
      drotate 4; dsplitp.
      drotate 5; dswap; dsubstp.
      do 5 (dswap; drotate 1); dswap; dsubstp.
      dsplitp; dclear.
      do 8 (dswap; drotate 1); dswap.
      duse_empty DSDistributeNand; dsplitp; dswap; dclear.
      eapply DSModusPonensP; first by dhead.
      dswap; dclear; dorp.
        do 5 (dswap; drotate 1); dsubstp.
        dnotp; first by apply DAPEqual.
      dswap; din_union_pr; simpl_embed.
      dorp; first by dswap; dnotp.
      din_cons_pl; simpl_embed.
      dorp; last by devalp.
      eapply DSEqualEvent.
      do 8 (dswap; drotate 1); dsplitp; do 2 (dsubstc; dclear);
        distinguish_variables; rewrite eq_refl.
      do 3 (dswap; drotate 1); dswap; dsubstc; distinguish_variables.
      by dassumption.

    (* Prove for indications *)
    difp.
      dforallc i Hf_i; dforallc e Hf_e; devalc.
      difc; dsplitp; dswap; dsplitp.
      ddestructp (fun t => {-A (Fs' ' Fn, Fors, Fois) = t -});
        dexistsp m_ Hf_m_; dexistsp n_ Hf_n_; dsplitp;
        dswap; dsubstp; devalp;
        ddestructpairp; repeat dsplitp.
      drotate 5; dsplitp.
      dswap; drotate 1; dswap; dsubstp.
      do 4 (dswap; drotate 1); dswap; dsubstp; dsplitp.
      by dnotp.

    (* Prove for periodics *)
    difp.
      devalc; difc; dsplitp; dswap; dsplitp.
      ddestructpairp; repeat dsplitp.
      do 2 (dswap; dclear); dswap.
      drotate 2; dsplitp; dswap; dclear; drotate 2; dsubstp.
      dswap; drotate 2; dsubstp; dswap; dclear; dsplitp.
      by dnotp; dsubstp.

    by devalp.
  -}

  (* By InvL *)
  dhave {-A
    self-event /\ on n', ((n, m) \in Fs' ' n') =>>
    (self-event /\ on n', (((n, m) \in Fs ' n')) \/
      on n', event[]-> CSLSend ' n ' m)
  -}.
  {
    repeat dclear. (* Clean up the context *)

    (* Instantiate InvL *)
    eapply DSCut; first by apply DSEmptyContext; apply DPInvL with (A := {-A
        on n', ((n, m) \in Fs' ' n') ->
        (on n', ((n, m) \in Fs ' n') \/
          on n', event[]-> CSLSend ' n ' m) -});
      first by repeat constructor.

    (* Prove for requests *)
    difp.
      dforallc e Hf_e; simpl_embed.
      difc; dsplitp; dsplitp; dswap; dsplitp.
      drotate 3; dsubstp; devalp.
      ddestructp (fun t => {-A (Fs' ' Fn, Fors, Fois) = t -});
        dexistsp m_ Hf_m_; dexistsp n_ Hf_n_; simpl_embed; dsplitp;
        dswap; dsubstp; devalp;
        ddestructpairp; repeat dsplitp.

      difc; dsplitp.
      dswap; drotate 1; dswap; dsubstp.
      do 7 (dswap; drotate 1); dswap; dsubstp.
      din_union_pr; simpl_embed; dswap; dclear; dorp;
        first by dleft; dsplitc; dassumption.
      dright; dsplitc; first by dassumption.
      din_cons_pl; simpl_embed; dorp; last by devalp.
      ddestructpairp; dsplitp; dsubstc; dclear; dsubstc;
        dclear; distinguish_variables; rewrite eq_refl.
      repeat (dsplitc; first by dassumption).
      by drotate 5; dsubstc; dassumption.

    (* Prove for indications *)
    difp.
      dforallc i Hf_i; dforallc e Hf_e; simpl_embed.
      difc; dsplitp; dsplitp; dswap; dsplitp.
      drotate 3; devalp.
      ddestructp (fun t => {-A (Fs' ' Fn, Fors, Fois) = t -});
        dexistsp m_ Hf_m_; dexistsp n_ Hf_n_; simpl_embed; dsplitp;
        dswap; dsubstp; devalp;
        ddestructpairp; repeat dsplitp.

      difc; dsplitp.
      dswap; drotate 1; dswap; dsubstp.
      dleft; dsplitc; first by dassumption.
      by do 7 (dswap; drotate 1); dswap; dsubstp.

    (* Prove for periodics *)
    difp.
      difc; dsplitp; dsplitp; dswap; dsplitp.
      drotate 3; devalp.

      difc; dsplitp; dleft; dsubstc.
      dsplitc; first by eapply DAPEqual.

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
    eapply DARewriteIffPL; first by apply DSAndCommutative with
      (Acl := {-A Fn = n' -})
      (Acr := {-A event[]-> CSLSend ' n ' m -}).
    eapply DARewriteIffPR; first by apply DSAndAssociative with
      (Al := {-A self-event -})
      (Am := {-A event[]-> CSLSend ' n ' m -})
      (Ar := {-A Fn = n' -}).
    eapply DARewriteIffPL; first by apply DSAndCommutative with
      (Acl := {-A self-event -})
      (Acr := {-A event[]-> CSLSend ' n ' m -}).
    simpl_embed; rewrite !andbF /=; simpl_embed.
    eapply DARewriteIffPL; first by duse_empty DPTopRequestSelfEliminate;
      dforallp {-t CSLSend ' n ' m -}; dhead.
    eapply DARewriteIffPL; first by apply DSAndCommutative with
      (Acl := {-A event[]-> CSLSend ' n ' m -})
      (Acr := {-A Fn = n' -}).
    by simpl_embed.
  -}

  (* By InvL *)
  dhave {-A
    self-event /\ on n', ((0, CFLSend ' n ' m) \in Fors) =>>
    self-event /\ on n', ((n, m) \in Fs' ' n')
  -}.
  {
    repeat dclear. (* Clean up the context *)

    (* Instantiate InvL *)
    eapply DSCut; first by apply DSEmptyContext; apply DPInvL with (A := {-A
        on n', ((0, CFLSend ' n ' m) \in Fors) ->
        on n', ((n, m) \in Fs' ' n')
      -}); first by repeat constructor.

    (* Prove for requests *)
    difp.
      dforallc e Hf_e; simpl_embed.
      difc; dsplitp; dsplitp; dswap; dsplitp.
      drotate 3; dsubstp; devalp.
      ddestructp (fun t => {-A (Fs' ' Fn, Fors, Fois) = t -});
        dexistsp m_ Hf_m_; dexistsp n_ Hf_n_; simpl_embed; dsplitp;
        dswap; dsubstp; devalp;
        ddestructpairp; repeat dsplitp.

      difc; dsplitp; dsplitc; first by dhead.
      dswap; do 2 (dswap; drotate 1); dsubstp.
      din_cons_pl; simpl_embed; dorp; last by devalp.
      ddestructpairp; dsplitp; dclear; apply DSEqualEvent.

      do 6 (dswap; dclear); drotate 1; dswap; dsubstp; dswap; dclear.
      dswap; dsplitp; dsubstc; dclear; dsubstc; dclear;
        distinguish_variables; rewrite eq_refl /eq_op /=; distinguish_variables.
      dsubstc.
      duse DAPInUnion;
        dforallp {-t Fs ' n' -};
        dforallp {-t [(n_, m_)] -};
        dforallp {-t (n_, m_) -};
        simpl_embed;
        dsplitp; dswap; dclear.
      by difp; first by dright; devalc.

    (* Prove for indications *)
    difp.
      dforallc i Hf_i; dforallc e Hf_e; simpl_embed.
      difc; dsplitp; dsplitp; dswap; dsplitp.
      drotate 3; dsubstp; devalp.
      ddestructp (fun t => {-A (Fs' ' Fn, Fors, Fois) = t -});
        dexistsp m_ Hf_m_; dexistsp n_ Hf_n_; simpl_embed; dsplitp;
        dswap; dsubstp; devalp;
        ddestructpairp; repeat dsplitp.

      difc; dsplitp; dsplitc; first by dhead.
      by dclear; dswap; drotate 1; dsubstp; devalp.

    (* Prove for periodics *)
    difp.
      difc; dsplitp; dswap; devalp.
      set tf := {-t fun: match: $$0 with:
        { ($, $) -> (0, CFLSend ' $$0 ' $$1) } -}.
      ddestructpairp; do 2 dsplitp.
      difc; dsplitp; dsplitc; first by dhead.
      dswap; dsubstp; drotate 2; dsubst; drotate 5.
      duse DAPInMap;
        dforallp tf; dforallp {-t (n, m) -}; dforallp {-t Fs ' Fn -}; simpl_embed.
      dsplitp; dclear; devalp; difp; first by
        dclear; dswap; drotate 4; dsubstp.
      dswap; drotate 1; dswap.
      dhave {-A Fs ' Fn = Fs' ' Fn -}; first by duse DAPEqualSymmetric;
        dforallp {-t Fs' ' Fn -}; dforallp {-t Fs ' Fn -}; simpl_embed;
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
    by simpl_embed.
  -}

  (* By (8) and (9) *)
  dhave {-A
    self-event /\ on n', ((0, CFLSend ' n ' m) \in Fors) =>>
    (self-event /\ on n', ((n, m) \in Fs ' n')) \/
      on n', event[]-> CSLSend ' n ' m
  -}.
  {
    eapply DARewriteEntailsP; first by dhead.
    by simpl_embed; rewrite /eq_op /= andbF.
  -}

  (* By (6) and (10) *)
  dhave {-A
    on n', event[0]-> CFLSend ' n ' m <~
    self-event /\ on n', ((n, m) \in Fs ' n') \/
    on n', event[]-> CSLSend ' n ' m
  -}.
  {
    drotate 4; eapply DARewriteEntailsP; first by drotate 5; dhead.
    by simpl_embed.
  -}

  (* By (7) and (11) *)
  dhave {-A
    on n', event[0]-> CFLSend ' n ' m <~
    on n', event[]-> CSLSend ' n ' m
  -}.
  {
    eapply DARewriteEntailsP; first by drotate 3; dhead.
    simpl_embed.
    eapply DARewriteIffPL; first by apply DSOrCommutative with
      (Acl := {-A eventuallyp^ on n', event[]-> CSLSend ' n ' m -})
      (Acr := {-A on n', event[]-> CSLSend ' n ' m -}).
    simpl_embed.
    eapply DARewriteCongruentCL; first by apply DTL83_1 with
      (A := {-A on n', event[]-> CSLSend ' n ' m -}).
    by simpl_embed.
  -}

  (* From (5) and (12) *)
  dhave {-A
    on n, event[]<- CSLDeliver ' n' ' m <~
    eventuallyp on n', event[]-> CSLSend ' n ' m
  -}.
  {
    drotate 7; eapply DARewriteEntailsP; first by drotate 4; dhead.
    by simpl_embed; rewrite /eq_op /= andbF.
  -}

  (* By lemma 83 on (9) *)
  (* NOTE: This line is missing from the paper proof *)
  dhave {-A
    on n, event[]<- CSLDeliver ' n' ' m <~
    on n', event[]-> CSLSend ' n ' m
  -}.
  {
    eapply DARewriteCongruentCL; first by apply DTL83_1 with
      (A := {-A on n', event[]-> CSLSend ' n ' m -}).
    by simpl_embed.
  -}

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
