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
Theorem SL_1 : empty_context |- stubborn_link, {A:
  forall: forall: forall: (* 2:n, 1:n', 0:m *)
  correct #2 /\ correct #1 ->
  on #2, event []-> CSLSend $ #1 $ #0 =>>
  always eventually on #1, event []<- CSLDeliver $ #2 $ #0
}.
Proof.
  (* Introduce context *)
  set C := stubborn_link; rewrite -/C /empty_context.
  d_forallc n Hf_n; d_forallc n' Hf_n'; d_forallc m Hf_m; simpl_embed.
  d_ifc; d_splitp.

  (* By IR *)
  d_have {A:
    on n, event []-> CSLSend $ n' $ m =>>
    self-event /\ (n', m) \in (Fs' $ n)
  }.
  {
    (* Instantiate IR *)
    d_use DPIR; d_forallp {t: CSLSend $ n' $ m}; d_evalp.

    d_destructpairp.

    Ltac dt_gen := eapply DTGeneralization; first by repeat constructor.
    d_have {A:
      on n, event []-> CSLSend $ n' $ m =>>
      event []-> CSLSend $ n' $ m
    }.
    {
      by dt_gen; d_ifc; d_splitp; d_assumption.
    }
    dt_trans; d_clear.

    d_have {A:
      (Fs' $ Fn = Fs $ Fn \union [(n', m)] /\
      Fors = [(0, CFLSend $ n' $ m)]) /\ Fois = [] =>>
      (n', m) \in Fs' $ Fn
    }.
    {
      dt_gen.
      d_ifc; d_splitp; d_splitp; d_substc.
      eapply DSCut; first by eapply DAPInUnion.
      d_forallp {t: Fs $ Fn};
        d_forallp {t: [(n', m)]};
        d_forallp {t: (n', m)};
        simpl_embed;
        d_splitp; d_swap; d_clear; d_ifp.
      d_right; eapply DAPIn; first by []; last by rewrite mem_seq1.
      by d_head.
    }

Lemma test_1 C Delta Gamma Ap Acl Acr :
  Context Delta Gamma |- C, {A:
    (Ap =>> Acl /\ Acr) <-> (Ap =>> Acl) /\ (Ap =>> Acr)
  }.
Proof.
Admitted. (* TODO *)

Lemma DSApplyC C Delta Gamma Ap Ac :
  Context Delta ({A: Ap -> Ac} :: Gamma) |- C, Ap ->
  Context Delta ({A: Ap -> Ac} :: Gamma) |- C, Ac.
Proof.
Admitted. (* TODO *)

Ltac d_apply_c := apply DSApplyC.

    match goal with
    | |- Context _ _ |- _, {A: ?_Ap =>> ?_Acl /\ ?_Acr} =>
      eapply DSCut; first (by apply test_1 with
        (Ap := _Ap)
        (Acl := _Acl)
        (Acr := _Acr));
      d_splitp; d_clear; d_apply_c; d_clear
    end.
    d_splitc.

    d_swap; dt_trans; d_clear.
    d_swap; eapply DARewriteIfP; first by d_head.
    simpl_embed.

    eapply DSCut; first by apply DSIfAndSplit with
      (Ap := {A: event []-> CSLSend $ n' $ m})
      (Acl := {A: self-event})
      (Acr := {A: (n', m) \in Fs' $ Fn}).
    d_splitp; d_swap; d_clear; d_ifp.
      d_splitc; last by d_splitp.
      d_use_empty DPTopRequestSelf.
      by d_forallp {t: CSLSend $ n' $ m}; d_splitp.

    do 4 (d_swap; d_clear). (* Clean up the context *)
    d_have {A: on n, event []-> CSLSend $ n' $ m -> self-event /\
      (n', m) \in Fs' $ n}.
      d_ifc; d_splitp; d_rotate 2.
      d_ifp; first by d_swap.
      by d_substp.

    d_have {A: on n, event []-> CSLSend $ n' $ m =>> self-event /\
      (n', m) \in Fs' $ n}.
    apply DTGeneralization; first by repeat constructor.
    d_head. d_head.
  }

  (* By InvS'' *)
  d_have {A:
    self-event /\ (n', m) \in (Fs' $ n) =>>
    always^ (self-event -> (n', m) \in (Fs $ n))
  }.
  {
    (* Instantiate InvS'' *)
    set S := {A: forall: (* 0:ts *) (n', m) \in #0}.
    eapply DSCut. repeat d_clear; apply DPInvS'' with (S0 := S);
      [by auto_is_closed | by repeat econstructor].
    d_forallp n; simpl_embed.

    (* Prove property for requests *)
    d_ifp.
      d_forallc s Hf_s; d_forallc e Hf_e;
        d_ifc; d_apply.
      eapply DARewriteIffPL; first by
        d_use DAPConcatIn; d_forallp {t: (n', m)}; d_forallp s; d_head.
      simpl_embed.

      d_existsp sl Hf_sl; d_existsp sr Hf_sr; simpl_embed.
      d_substc; distinguish_variables.
      d_evalc.
      d_destructc (fun t => {A: (n', m) \in
        match: t with: {{(#, #, #) -> #0}}}); rewrite /=.
      d_forallc m'' Hf_m''; d_forallc n'' Hf_n''; simpl_embed.
      d_ifc; d_substc; distinguish_variables; d_evalc.

      d_use DAPInUnion.
      d_forallp {t: sl ++ [(n', m)] ++ sr};
        d_forallp {t: [(n'', m'')]};
        d_forallp {t: (n', m)}; simpl_embed.
      d_splitp; d_swap; d_clear; d_ifp.
        d_left.
        d_use DAPInConcat.
        d_forallp sl;
          d_forallp {t: [(n', m)] ++ sr};
          d_forallp {t: (n', m)}; simpl_embed.
        d_ifp.
          d_right.
          d_use DAPInConcat.
          d_forallp {t: [(n', m)]};
            d_forallp sr;
            d_forallp {t: (n', m)}; simpl_embed.
          d_ifp; first by d_left; eapply DAPIn; first by []; last by rewrite mem_seq1.
          d_head.
        d_head.

      d_head.

    (* Prove property for indications *)
    d_ifp.
      d_forallc s Hf_s; d_forallc i Hf_i; d_forallc e Hf_e;
        d_ifc; d_apply.

      d_evalc.
      d_destructc (fun t => {A: (n', m) \in
        match: t with: {{(#, #, #) -> #0}}}); rewrite /=.
      d_forallc m'' Hf_m''; d_forallc n'' Hf_n''; simpl_embed.
      d_ifc; d_substc; distinguish_variables.
      by d_evalc; d_clear.

    (* Prove property for periodics *)
    d_ifp.
      by d_forallc s Hf_s; d_ifc; d_evalc; d_applyp.

    by d_evalp.
  }

  (* From (2) and (3) *)
  d_have {A:
    on n, event []-> CSLSend $ n' $ m =>>
    always^ (self-event -> (n', m) \in (Fs $ n))
  }.
  {
    d_rotate 1; eapply DARewriteEntailsP; first by d_rotate 2.
    simpl_embed.
    by dt_trans; d_assumption.
  }

  (* By APerSA *)
  d_have {A:
    correct n -> (self-event -> (n', m) \in (Fs $ n)) =>>
    always eventually on n,
      (self-event /\ (0, CFLSend $ n' $ m) \in Fors)
  }.
  {
    d_ifc; d_clear.

    (* Instantiate APerSA *)
    set S := {A: forall: (* 0:ts *) (n', m) \in #0}.
    set A := {A: on n,
      (self-event /\ (0, CFLSend $ n' $ m) \in Fors)}.
    eapply DSCut. repeat d_clear; apply DPAPerSA with (S := S) (A := A);
      [by auto_is_closed | by repeat econstructor | by repeat econstructor].
    d_forallp n; d_evalp; simpl_embed.

    d_ifp.
      d_ifc; do 3 (d_splitp; d_swap).
      d_evalp.
      set tf := {t: fun:
          match: #0 with:
          {{ (#, #) -> (0, CFLSend $ #0 $ #1) }}
        };
        d_destructpairp; do 2 d_splitp.

      d_splitc; first by d_assumption.
      d_splitc; first by d_assumption.
      d_swap; d_substc.
      d_use DAPInMap.
      d_forallp tf; d_forallp {t: (n', m)};
        d_forallp {t: Fs $ n};
        simpl_embed.
      d_splitp; d_swap; d_clear; d_ifp; first by d_assumption.
      by d_evalp.

    d_ifp; first by d_assumption.
    by d_evalp.
  }

  (* From (4) and (5) *)
  d_have {A:
    on n, event []-> CSLSend $ n' $ m =>>
    always^ eventually on n,
      (self-event /\ (0, CFLSend $ n' $ m) \in Fors)
  }.
  {
    d_ifp; first by d_assumption.
    d_rotate 1; eapply DARewriteEntailsP; first by d_rotate 4; d_head.
    simpl_embed.
    eapply DARewriteCongruentCR; first by apply DTL119 with (A := {A:
      eventually on n,
        (self-event /\ (0, CFLSend $ n' $ m) \in Fors)
      }).
    by simpl_embed.
  }

  (* From OR *)
  (* NOTE: send_fl(n, m) should be send_fl(n', m) *)
  d_have {A:
    on n, (self-event /\ (0, CFLSend $ n' $ m) \in Fors) =>>
    eventually^ on n, event [0]-> CFLSend $ n' $ m
  }.
  {
    (* Instantiate OR *)
    by d_use DPOR;
      d_forallp n; d_forallp 0; d_forallp {t: CFLSend $ n' $ m}.
  }

  (* From (6) and (7) *)
  (* NOTE: send_fl(n, m) should be send_fl(n', m) *)
  d_have {A:
    on n, event []-> CSLSend $ n' $ m =>>
    always^ eventually eventually^ on n, event [0]-> CFLSend $ n' $ m
  }.
  {
    d_rotate 1; eapply DARewriteEntailsP;
      first by d_rotate 6; d_head.
    by simpl_embed; rewrite andbF.
  }

  (* From lemma 120 on (8) *)
  (* NOTE: Lemma 84 does not apply here; must use new lemma 120 instead *)
  d_have {A:
    on n, event []-> CSLSend $ n' $ m =>>
      always^ eventually^ on n, event [0]-> CFLSend $ n' $ m
  }.
  {
    eapply DARewriteEntailsP; first by apply DTL120_3 with (A := {A:
      on n, event [0]-> CFLSend $ n' $ m}).
    by simpl_embed.
  }

  (* By rule FLoss on (1) and (9) *)
  d_have {A:
    on n, event []-> CSLSend $ n' $ m =>>
    always^ eventually^ on n', event [0]<- CFLDeliver $ n $ m
  }.
  {
    (* Instantiate FLoss *)
    d_use DPFLoss.
    d_forallp n; d_forallp n'; d_forallp m; d_forallp 0.
    d_ifp; first by d_assumption.

    d_rotate 1; eapply DARewriteIfP;
      first by by d_rotate 9; d_head.
    by simpl_embed.
  }

  (* From rule IIOI *)
  d_have {A:
    on n', event [0]<- CFLDeliver $ n $ m =>>
    eventually^ on n', event []<- CSLDeliver $ n $ m
  }.
  {
    (* Instantiate IIOI *)
    eapply DSCut. repeat d_clear; eapply DPIIOI with (S0 := {A: forall: ATrue});
      [by auto_is_closed | by repeat econstructor].
    d_forallp n'; d_forallp 0; d_forallp {t: CFLDeliver $ n $ m};
      d_forallp {t: CSLDeliver $ n $ m}; simpl_embed.
    d_ifp.
      d_forallc s Hf_s; simpl_embed; d_splitc; first by d_applyc; d_notc.
      by d_evalc.
    d_evalp.

    eapply DARewriteIffCR; first by eapply DSAndElimination with (A :=
      {A: on n', event [0]<- CFLDeliver $ n $ m}).
    by simpl_embed; rewrite andbF.
  }

  (* From (10) and (11) *)
  d_have {A:
    on n, event []-> CSLSend $ n' $ m =>>
    always^ eventually^ eventually^
      on n', event []<- CSLDeliver $ n $ m
  }.
  {
    d_rotate 1; eapply DARewriteEntailsP;
      first by d_rotate 10; d_head.
    by simpl_embed; rewrite andbF.
  }

  (* From lemma 84 and (12) *)
  (* NOTE: Lemma 84 does not apply here; must use new lemma 120 instead *)
  d_have {A:
    on n, event []-> CSLSend $ n' $ m =>>
    always^ eventually^
      on n', event []<- CSLDeliver $ n $ m
  }.
  {
    eapply DARewriteEntailsP; first by apply DTL120_2 with (A := {A:
      on n', event []<- CSLDeliver $ n $ m}).
    by simpl_embed.
  }

  eapply DARewriteIfP; first by apply DTL121 with (A := {A:
    on n', event []<- CSLDeliver $ n $ m}).
  simpl_embed.
  eapply DARewriteIfP; first by apply DTL122 with (A := {A:
    on n', event []<- CSLDeliver $ n $ m}).
  by simpl_embed.
Qed.

(* No-forge
 * If a node n delivers a message m with sender n', then m was previously sent
 * to n by n' *)
Theorem SL_2 : empty_context |- stubborn_link, {A:
  forall: forall: forall: (* 2:n, 1:n', 0:m *)
  on #2, event []<- {t: CSLDeliver $ #1 $ #0} <~
  on #1, event []-> {t: CSLSend $ #2 $ #0}
}.
Proof.
  (* Introduce context *)
  set C := stubborn_link; rewrite -/C /empty_context.
  d_forallc n Hf_n; d_forallc n' Hf_n'; d_forallc m Hf_m; simpl_embed.

  (* By OI' *)
  d_have {A:
    on n, event []<- CSLDeliver $ n' $ m =>>
    eventuallyp (self-event /\ on n, (CSLDeliver $ n' $ m \in Fois))
  }.
  {
    (* Instantiate OI' *)
    d_use DPOI'; d_forallp n; d_forallp {t: CSLDeliver $ n' $ m}; simpl_embed.

    eapply DARewriteIfP; first by apply DTL123 with (A := {A:
      self-event /\ on n, (CSLDeliver $ n' $ m \in Fois)}).
    by simpl_embed.
  }

  (* By InvL *)
  d_have {A:
    self-event /\ on n, (CSLDeliver $ n' $ m \in Fois) =>>
    on n, event [0]<- CFLDeliver $ n' $ m
  }.
  {
    d_clear. (* Clean up the context *)

    (* Instantiate InvL *)
    eapply DSCut; first by apply DSEmptyContext; apply DPInvL with (A := {A:
        on n, (CSLDeliver $ n' $ m \in Fois) ->
        on n, event [0]<- CFLDeliver $ n' $ m
      }); first by repeat constructor.

    (* Prove for requests *)
    d_ifp.
      (* Obtain the first contradictory premise *)
      d_forallc e Hf_e; simpl_embed.
      d_ifc; d_splitp; d_swap; d_evalp.
      d_destructp (fun t => {A: (Fs' $ Fn, Fors, Fois) = t});
        d_existsp m_ Hf_m_; d_existsp n'_ Hf_n'_; d_splitp; d_swap;
        d_substp; d_evalp.
      d_destructpairp; do 2 d_splitp.
      do 2 d_clear; do 2 (d_swap; d_clear). (* Clean up the context *)

      (* Obtain the second contradictory premise *)
      by d_ifc; d_splitp; d_clear; d_substp; d_evalp.


    (* Prove for indications *)
    d_ifp.
      d_forallc i Hf_i; d_forallc e Hf_e; simpl_embed.
      d_ifc; d_splitp; d_swap; d_evalp.
      d_destructp (fun t => {A: (Fs' $ Fn, Fors, Fois) = t});
        d_existsp m_ Hf_m_; d_existsp n'_ Hf_n'_; d_splitp; d_swap;
        d_subst; d_evalp.
      d_destructpairp; do 2 d_splitp.
      d_ifc; d_splitp.
      d_splitc; first by d_head.
      d_swap; do 3 (d_swap; d_rotate 1); d_substp.
      d_in_cons_pl; simpl_embed.
      d_orp; last by d_evalp.
      eapply DSEqualEvent; d_splitp.
      d_substc; d_clear; d_substc; d_clear;
        distinguish_variables; rewrite eq_refl.
      d_clear; d_destructpairp; d_splitp; d_rotate 2; do 3 (d_swap; d_clear).
      by do 2 (d_substp; d_swap; d_clear);
        distinguish_variables; rewrite eq_refl.

    (* Prove for periodics *)
    d_ifp.
      (* Obtain the first contradictory premise *)
      d_ifc; d_splitp; d_swap; d_evalp.
      d_destructpairp; repeat d_splitp.
      do 2 d_clear; (d_swap; d_clear). (* Clean up the context *)

      (* Obtain the second contradictory premise *)
      by d_ifc; d_splitp; d_clear; d_substp; d_evalp.

    eapply DARewriteIffPL; first by apply DSMergeIf with
      (Ap1 := {A: self-event})
      (Ap2 := {A: on n, (CSLDeliver $ n' $ m \in Fois)})
      (Ac := {A: on n, event [0]<- CFLDeliver $ n' $ m}).
    by simpl_embed.
  }

  (* From (1) and (2) *)
  d_have {A:
    on n, event []<- CSLDeliver $ n' $ m <~
    on n, event [0]<- CFLDeliver $ n' $ m
  }.
  {
    d_rotate 1; eapply DARewriteEntailsP; first by d_head.
    by simpl_embed.
  }

  (* By NForge *)
  d_have {A:
    on n, event [0]<- CFLDeliver $ n' $ m <~
    on n', event [0]-> CFLSend $ n $ m
  }.
  {
    (* Instantiate NForge *)
    by d_use DPNForge;
      d_forallp n'; d_forallp n; d_forallp m; d_forallp 0.
  }

  (* By lemma 85 on (3) and (4) *)
  d_have {A:
    on n, event []<- CSLDeliver $ n' $ m <~
    on n', event [0]-> CFLSend $ n $ m
  }.
  {
    by eapply DTL85; first by d_rotate 1; d_head.
  }

  (* By OR' *)
  d_have {A:
    on n', event [0]-> CFLSend $ n $ m =>>
    eventuallyp (self-event /\ on n',
      ((0, CFLSend $ n $ m) \in Fors))
  }.
  {
    (* Instantiate OR' *)
    d_use DPOR';
      d_forallp n'; d_forallp 0; d_forallp {t: CFLSend $ n $ m}; simpl_embed.

    eapply DARewriteIfP; first by apply DTL123 with (A := {A:
      self-event /\ on n', ((0, CFLSend $ n $ m) \in Fors)}).
    by simpl_embed.
  }

  (* By InvSA *)
  d_have {A:
    self-event /\ on n', ((n, m) \in Fs $ n') =>>
    eventuallyp^ on n', event []-> CSLSend $ n $ m
  }.
  {
    do 6 d_clear. (* Clean up the context *)

    (* Instantiate InvSA *)
    eapply DSCut; first by apply DPInvSA with
      (S0 := {A: forall: (* 0:ts *) on n', ((n, m) \in #0)})
      (A := {A: event []-> CSLSend $ n $ m});
      [by auto_is_closed | by repeat econstructor | by repeat econstructor].
    d_forallp n'; simpl_embed.

    (* Prove for initialization *)
    d_ifp.
      d_evalc.
      by d_notc; d_splitp; d_assumption.

    (* Prove for requests *)
    d_ifp.
      d_forallc e Hf_e; d_evalc.
      d_ifc; d_splitp; d_splitp; do 2 (d_swap; d_splitp).
      d_splitc; first by d_assumption.
      d_splitc; first by d_assumption.
      d_rotate 4; d_splitp.
      d_destructp (fun t => {A: (Fs' $ Fn, Fors, Fois) = t});
        d_existsp m_ Hf_m_; d_existsp n_ Hf_n_; d_splitp;
        d_swap; d_substp; d_evalp;
        d_destructpairp; repeat d_splitp.
      d_rotate 4; d_splitp.
      d_rotate 5; d_swap; d_substp.
      do 5 (d_swap; d_rotate 1); d_swap; d_substp.
      d_splitp; d_clear.
      do 8 (d_swap; d_rotate 1); d_swap.
      d_use_empty DSDistributeNand; d_splitp; d_swap; d_clear.
      eapply DSModusPonensP; first by d_head.
      d_swap; d_clear; d_orp.
        do 5 (d_swap; d_rotate 1); d_substp.
        d_notp; first by apply DAPEqual.
      d_swap; d_in_union_pr; simpl_embed.
      d_orp; first by d_swap; d_notp.
      d_in_cons_pl; simpl_embed.
      d_orp; last by d_evalp.
      eapply DSEqualEvent.
      do 8 (d_swap; d_rotate 1); d_splitp; do 2 (d_substc; d_clear);
        distinguish_variables; rewrite eq_refl.
      do 3 (d_swap; d_rotate 1); d_swap; d_substc; distinguish_variables.
      by d_assumption.

    (* Prove for indications *)
    d_ifp.
      d_forallc i Hf_i; d_forallc e Hf_e; d_evalc.
      d_ifc; d_splitp; d_swap; d_splitp.
      d_destructp (fun t => {A: (Fs' $ Fn, Fors, Fois) = t});
        d_existsp m_ Hf_m_; d_existsp n_ Hf_n_; d_splitp;
        d_swap; d_substp; d_evalp;
        d_destructpairp; repeat d_splitp.
      d_rotate 5; d_splitp.
      d_swap; d_rotate 1; d_swap; d_substp.
      do 4 (d_swap; d_rotate 1); d_swap; d_substp; d_splitp.
      by d_notp.

    (* Prove for periodics *)
    d_ifp.
      d_evalc; d_ifc; d_splitp; d_swap; d_splitp.
      d_destructpairp; repeat d_splitp.
      do 2 (d_swap; d_clear); d_swap.
      d_rotate 2; d_splitp; d_swap; d_clear; d_rotate 2; d_substp.
      d_swap; d_rotate 2; d_substp; d_swap; d_clear; d_splitp.
      by d_notp; d_substp.

    by d_evalp.
  }

  (* By InvL *)
  d_have {A:
    self-event /\ on n', ((n, m) \in Fs' $ n') =>>
    (self-event /\ on n', (((n, m) \in Fs $ n')) \/
      on n', event []-> CSLSend $ n $ m)
  }.
  {
    repeat d_clear. (* Clean up the context *)

    (* Instantiate InvL *)
    eapply DSCut; first by apply DSEmptyContext; apply DPInvL with (A := {A:
        on n', ((n, m) \in Fs' $ n') ->
        (on n', ((n, m) \in Fs $ n') \/
          on n', event []-> CSLSend $ n $ m)});
      first by repeat constructor.

    (* Prove for requests *)
    d_ifp.
      d_forallc e Hf_e; simpl_embed.
      d_ifc; d_splitp; d_splitp; d_swap; d_splitp.
      d_rotate 3; d_substp; d_evalp.
      d_destructp (fun t => {A: (Fs' $ Fn, Fors, Fois) = t});
        d_existsp m_ Hf_m_; d_existsp n_ Hf_n_; simpl_embed; d_splitp;
        d_swap; d_substp; d_evalp;
        d_destructpairp; repeat d_splitp.

      d_ifc; d_splitp.
      d_swap; d_rotate 1; d_swap; d_substp.
      do 7 (d_swap; d_rotate 1); d_swap; d_substp.
      d_in_union_pr; simpl_embed; d_swap; d_clear; d_orp;
        first by d_left; d_splitc; d_assumption.
      d_right; d_splitc; first by d_assumption.
      d_in_cons_pl; simpl_embed; d_orp; last by d_evalp.
      d_destructpairp; d_splitp; d_substc; d_clear; d_substc;
        d_clear; distinguish_variables; rewrite eq_refl.
      repeat (d_splitc; first by d_assumption).
      by d_rotate 5; d_substc; d_assumption.

    (* Prove for indications *)
    d_ifp.
      d_forallc i Hf_i; d_forallc e Hf_e; simpl_embed.
      d_ifc; d_splitp; d_splitp; d_swap; d_splitp.
      d_rotate 3; d_evalp.
      d_destructp (fun t => {A: (Fs' $ Fn, Fors, Fois) = t});
        d_existsp m_ Hf_m_; d_existsp n_ Hf_n_; simpl_embed; d_splitp;
        d_swap; d_substp; d_evalp;
        d_destructpairp; repeat d_splitp.

      d_ifc; d_splitp.
      d_swap; d_rotate 1; d_swap; d_substp.
      d_left; d_splitc; first by d_assumption.
      by do 7 (d_swap; d_rotate 1); d_swap; d_substp.

    (* Prove for periodics *)
    d_ifp.
      d_ifc; d_splitp; d_splitp; d_swap; d_splitp.
      d_rotate 3; d_evalp.

      d_ifc; d_splitp; d_left; d_substc.
      d_splitc; first by eapply DAPEqual.

      d_rotate 2; do 3 (d_swap; d_clear); d_substp.
      d_destructpairp; do 2 d_splitp; do 3 (d_swap; d_clear); d_swap; d_substp.
      by d_assumption.

    eapply DARewriteIffPL; first by apply DSMergeIf with
      (Ap1 := {A: self-event})
      (Ap2 := {A: on n', ((n, m) \in Fs' $ n')})
      (Ac := {A: on n', (((n, m) \in Fs $ n')) \/
        on n', event []-> CSLSend $ n $ m}).
    eapply DARewriteIffPL; first by apply DSIfAndIntroduce with
      (Apl := {A: self-event})
      (Apr := {A: on n', ((n, m) \in Fs' $ n')})
      (Ac := {A: on n', ((n, m) \in Fs $ n') \/
        on n', event []-> CSLSend $ n $ m}).
    eapply DARewriteIffPL; first by apply DSOrDistributesAnd with
      (Al := {A: on n', ((n, m) \in Fs $ n')})
      (Ar := {A: on n', event []-> CSLSend $ n $ m})
      (A := {A: self-event}).
    eapply DARewriteIffPL; first by apply DSAndCommutative with
      (Acl := {A: Fn = n'})
      (Acr := {A: event []-> CSLSend $ n $ m}).
    eapply DARewriteIffPR; first by apply DSAndAssociative with
      (Al := {A: self-event})
      (Am := {A: event []-> CSLSend $ n $ m})
      (Ar := {A: Fn = n'}).
    eapply DARewriteIffPL; first by apply DSAndCommutative with
      (Acl := {A: self-event})
      (Acr := {A: event []-> CSLSend $ n $ m}).
    simpl_embed; rewrite !andbF /=; simpl_embed.
    eapply DARewriteIffPL; first by d_use_empty DPTopRequestSelfEliminate;
      d_forallp {t: CSLSend $ n $ m}; d_head.
    eapply DARewriteIffPL; first by apply DSAndCommutative with
      (Acl := {A: event []-> CSLSend $ n $ m})
      (Acr := {A: Fn = n'}).
    by simpl_embed.
  }

  (* By InvL *)
  d_have {A:
    self-event /\ on n', ((0, CFLSend $ n $ m) \in Fors) =>>
    self-event /\ on n', ((n, m) \in Fs' $ n')
  }.
  {
    repeat d_clear. (* Clean up the context *)

    (* Instantiate InvL *)
    eapply DSCut; first by apply DSEmptyContext; apply DPInvL with (A := {A:
        on n', ((0, CFLSend $ n $ m) \in Fors) ->
        on n', ((n, m) \in Fs' $ n')
      }); first by repeat constructor.

    (* Prove for requests *)
    d_ifp.
      d_forallc e Hf_e; simpl_embed.
      d_ifc; d_splitp; d_splitp; d_swap; d_splitp.
      d_rotate 3; d_substp; d_evalp.
      d_destructp (fun t => {A: (Fs' $ Fn, Fors, Fois) = t});
        d_existsp m_ Hf_m_; d_existsp n_ Hf_n_; simpl_embed; d_splitp;
        d_swap; d_substp; d_evalp;
        d_destructpairp; repeat d_splitp.

      d_ifc; d_splitp; d_splitc; first by d_head.
      d_swap; do 2 (d_swap; d_rotate 1); d_substp.
      d_in_cons_pl; simpl_embed; d_orp; last by d_evalp.
      d_destructpairp; d_splitp; d_clear; apply DSEqualEvent.

      do 6 (d_swap; d_clear); d_rotate 1; d_swap; d_substp; d_swap; d_clear.
      d_swap; d_splitp; d_substc; d_clear; d_substc; d_clear;
        distinguish_variables; rewrite eq_refl /eq_op /=; distinguish_variables.
      d_substc.
      d_use DAPInUnion;
        d_forallp {t: Fs $ n'};
        d_forallp {t: [(n_, m_)]};
        d_forallp {t: (n_, m_)};
        simpl_embed;
        d_splitp; d_swap; d_clear.
      by d_ifp; first by d_right; d_evalc.

    (* Prove for indications *)
    d_ifp.
      d_forallc i Hf_i; d_forallc e Hf_e; simpl_embed.
      d_ifc; d_splitp; d_splitp; d_swap; d_splitp.
      d_rotate 3; d_substp; d_evalp.
      d_destructp (fun t => {A: (Fs' $ Fn, Fors, Fois) = t});
        d_existsp m_ Hf_m_; d_existsp n_ Hf_n_; simpl_embed; d_splitp;
        d_swap; d_substp; d_evalp;
        d_destructpairp; repeat d_splitp.

      d_ifc; d_splitp; d_splitc; first by d_head.
      by d_clear; d_swap; d_rotate 1; d_substp; d_evalp.

    (* Prove for periodics *)
    d_ifp.
      d_ifc; d_splitp; d_swap; d_evalp.
      set tf := {t: fun: match: #0 with:
        {{ (#, #) -> (0, CFLSend $ #0 $ #1) }}}.
      d_destructpairp; do 2 d_splitp.
      d_ifc; d_splitp; d_splitc; first by d_head.
      d_swap; d_substp; d_rotate 2; d_subst; d_rotate 5.
      d_use DAPInMap;
        d_forallp tf; d_forallp {t: (n, m)}; d_forallp {t: Fs $ Fn}; simpl_embed.
      d_splitp; d_clear; d_evalp; d_ifp; first by
        d_clear; d_swap; d_rotate 4; d_substp.
      d_swap; d_rotate 1; d_swap.
      d_have {A: Fs $ Fn = Fs' $ Fn}; first by d_use DAPEqualSymmetric;
        d_forallp {t: Fs' $ Fn}; d_forallp {t: Fs $ Fn}; simpl_embed;
        d_splitp; d_ifp; d_assumption.
      by d_swap; d_clear; d_swap; d_substp; do 5 (d_swap; d_clear); d_substp.

    eapply DARewriteIffPL; first by apply DSMergeIf with
      (Ap1 := {A: self-event})
      (Ap2 := {A: on n', ((0, CFLSend $ n $ m) \in Fors)})
      (Ac := {A: on n', ((n, m) \in Fs' $ n')}).
    eapply DARewriteIffPL; first by apply DSIfAndIntroduce with
      (Apl := {A: self-event})
      (Apr := {A: on n', ((0, CFLSend $ n $ m) \in Fors)})
      (Ac := {A: on n', ((n, m) \in Fs' $ n')}).
    by simpl_embed.
  }

  (* By (8) and (9) *)
  d_have {A:
    self-event /\ on n', ((0, CFLSend $ n $ m) \in Fors) =>>
    (self-event /\ on n', ((n, m) \in Fs $ n')) \/
      on n', event []-> CSLSend $ n $ m
  }.
  {
    eapply DARewriteEntailsP; first by d_head.
    by simpl_embed; rewrite /eq_op /= andbF.
  }

  (* By (6) and (10) *)
  d_have {A:
    on n', event [0]-> CFLSend $ n $ m <~
    self-event /\ on n', ((n, m) \in Fs $ n') \/
    on n', event []-> CSLSend $ n $ m
  }.
  {
    d_rotate 4; eapply DARewriteEntailsP; first by d_rotate 5; d_head.
    by simpl_embed.
  }

  (* By (7) and (11) *)
  d_have {A:
    on n', event [0]-> CFLSend $ n $ m <~
    on n', event []-> CSLSend $ n $ m
  }.
  {
    eapply DARewriteEntailsP; first by d_rotate 3; d_head.
    simpl_embed.
    eapply DARewriteIffPL; first by apply DSOrCommutative with
      (Acl := {A: eventuallyp^ on n', event []-> CSLSend $ n $ m})
      (Acr := {A: on n', event []-> CSLSend $ n $ m}).
    simpl_embed.
    eapply DARewriteCongruentCL; first by apply DTL83_1 with
      (A := {A: on n', event []-> CSLSend $ n $ m}).
    by simpl_embed.
  }

  (* From (5) and (12) *)
  d_have {A:
    on n, event []<- CSLDeliver $ n' $ m <~
    eventuallyp on n', event []-> CSLSend $ n $ m
  }.
  {
    d_rotate 7; eapply DARewriteEntailsP; first by d_rotate 4; d_head.
    by simpl_embed; rewrite /eq_op /= andbF.
  }

  (* By lemma 83 on (9) *)
  (* NOTE: This line is missing from the paper proof *)
  d_have {A:
    on n, event []<- CSLDeliver $ n' $ m <~
    on n', event []-> CSLSend $ n $ m
  }.
  {
    eapply DARewriteCongruentCL; first by apply DTL83_1 with
      (A := {A: on n', event []-> CSLSend $ n $ m}).
    by simpl_embed.
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
