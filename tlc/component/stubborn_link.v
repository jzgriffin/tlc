Require Import mathcomp.ssreflect.eqtype.
Require Import mathcomp.ssreflect.seq.
Require Import mathcomp.ssreflect.ssrbool.
Require Import mathcomp.ssreflect.ssreflect.
Require Import tlc.component.component.
Require Import tlc.logic.all_logic.
Require Import tlc.operation.orientation.
Require Import tlc.operation.periodic_event.
Require Import tlc.semantics.all_semantics.
Require Import tlc.syntax.all_syntax.
Require Import tlc.utility.result.
Require Import tlc.utility.partial_map.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Stubborn link component *)
Definition stubborn_link :=
  let flc := 0 in
  Component
  (* initialize *)
  {t: fun:
    (* #0 = n *)
    []
  }
  (* request *)
  {t: fun: fun: fun:
    (* #(0, 0) = ir *)
    (* #(1, 0) = s *)
    (* #(2, 0) = n *)
    match: #0 with: CSLSend $ # $ #
    then:
      (* #(0, 0) = n' *)
      (* #(0, 1) = m *)
      (#(2, 0) \union [(#0, #1)],
        [(flc, CFLSend $ #0 $ #1)],
        [])
    else: TFailure
  }
  (* indication *)
  {t: fun: fun: fun:
    (* #(0, 0) = ii *)
    (* #(1, 0) = s *)
    (* #(2, 0) = n' *)
    match: #0 with: (flc, CFLDeliver $ # $ #)
    then:
      (* #(0, 0) = n *)
      (* #(0, 1) = m *)
      (#(2, 0), [], [CSLDeliver $ #0 $ #1])
    else: TFailure
  }
  (* periodic *)
  {t: fun: fun:
    (* #(0, 0) = s *)
    (* #(1, 0) = n *)
    let: # := (fun: let: (#, #) := #0 in:
      (flc, CFLSend $ #0 $ #1)) <$> #(0, 0) in:
    (#(1, 0), #0, [])
  }.

(* Specification *)

(* Stubborn delivery
 * If a correct node n sends a message m to a correct node n',
 * then n' deliver m infinitely often *)
Theorem SL_1 : [::] |- stubborn_link, {A:
  correct "n" /\ correct "n'" ->
  when-on["n"] when[]-> CSLSend $ "n'" $ "m" =>>
  always eventually when-on["n'"] when[]<- CSLDeliver $ "n" $ "m"
}.
Proof.
  (* Introduce assumptions *)
  apply DSIfC, DSAndP.
  pose Gamma := [:: {A: correct "n"}; {A: correct "n'"}]; rewrite -/Gamma.
  pose C := stubborn_link; rewrite -/C.

  (* By IR *)
  have H2 : Gamma |- C, {A:
    when-on["n"] when[]-> CSLSend $ "n'" $ "m" =>>
    when-self /\ ("n'", "m") \in ("Fs'" $ "n")
  }.
  {
    (* Generalize the strong implication to material implication
     * and move the antecedent into the premises *)
    apply DTGeneralization, DSIfC.

    (* Split the conjunctions in the premises and conclusion and immediately
     * prove when-self *)
    apply DSAndP, DSExchange, DSAndP, DSExchange, DSAndP, DSAndC;
      first by apply DSOrCR, DSOrCL, DSAndC; by apply DAnyAxiom.

    (* Instantiate IR *)
    have HIR := DPIR C Gamma {t: CSLSend $ "n'" $ "m"};
      eapply DAEvaluateC' in HIR; last by [].
    eapply DSCut; first by do 4 apply DSThin; apply HIR. clear HIR.
    apply DEntailsModusPonensP.
    + apply DSAndC; first by apply DAnyAxiom.
      apply DSAndC; first by apply DAnyAxiom.
      by apply DAnyAxiom.
    do 2 apply DAInjectivePairP.
    apply DASubstituteP; rewrite /=.
    apply DASubstituteC; rewrite /=.
    apply DInUnion, DSOrCR.
    eapply DAEvaluateC; first by [].
    by eapply DAPIn.
  }

  (* By InvS'' *)
  have H3 : Gamma |- C, {A:
    when-self /\ ("n'", "m") \in ("Fs'" $ "n") =>>
    always^ (when-self -> ("n'", "m") \in ("Fs" $ "n"))
  }.
  {
    set S := fun ts => {A: ("n'", "m") \in ts}.
    have HInvS'' := @DPInvS'' C Gamma S "n".

    have HSr : Gamma |- C, {A:
      forall: "s", forall: "e",
      S "s" ->
      S {t: let: (#, %, %) := request C $ "n" $ "s" $ "e" in: #0}
    }.
    apply DSForAllC with (t := "s"),
      DSForAllC with (t := {t: CSLSend $ "en" $ "em"});
      rewrite /instantiate_assertion /=.
    repeat rewrite -/(TPair "n'" "m");
    repeat rewrite -/(AIn {t: ("n'", "m")} _);
    repeat rewrite -/(AIf (("n'", "m") \in _) _).
    apply DSIfC.
    apply (DARewriteIffPL (DConcatIn _ _ {t: ("n'", "m")} "s"));
      rewrite /rewrite_assertion_any /=.
    apply DSExistsP with (t := "sl"),
      DSExistsP with (t := "sr");
      rewrite /instantiate_assertion /=.
    apply DASubstituteC; eapply DAEvaluateC; first by [].
    by apply DInUnion, DSOrCL, DInConcat, DSOrCR, DInConcat, DSOrCL;
      eapply DAPIn.

    have HSi : Gamma |- C, {A:
      forall: "s", forall: "i", forall: "e",
      S "s" ->
      S {t: let: (#, %, %) := indication C $ "n" $ "s" $ ("i", "e") in: #0}
    }.
    apply DSForAllC with (t := "s"),
      DSForAllC with (t := 0),
      DSForAllC with (t := {t: CFLDeliver $ "en" $ "em"});
      rewrite /instantiate_assertion /=.
    repeat rewrite -/(TPair "n'" "m");
    repeat rewrite -/(AIn {t: ("n'", "m")} _);
    repeat rewrite -/(AIf (("n'", "m") \in _) _).
    by apply DSIfC; eapply DAEvaluateC.

    have HSp : Gamma |- C, {A:
      forall: "s",
      S "s" ->
      S {t: let: (#, %, %) := periodic C $ "n" $ "s" in: #0}
    }.
    apply DSForAllC with (t := "s");
      rewrite /instantiate_assertion /=.
    repeat rewrite -/(TPair "n'" "m");
    repeat rewrite -/(AIn {t: ("n'", "m")} _);
    repeat rewrite -/(AIf (("n'", "m") \in _) _).
    by apply DSIfC; eapply DAEvaluateC.

    by specialize (HInvS'' HSr HSi HSp).
  }

  (* From H2 and H3 *)
  have H4 : Gamma |- C, {A:
    when-on["n"] when[]-> CSLSend $ "n'" $ "m" =>>
    always^ (when-self -> ("n'", "m") \in ("Fs" $ "n"))
  }.
  {
    by eapply DARewriteEntailsC' in H2; last (by apply H3).
  }

  (* By rule APerSA *)
  have H5 : Gamma |- C, {A:
    correct "n" -> (when-self -> ("n'", "m") \in ("Fs" $ "n")) =>>
    always eventually when-on["n"]
      (when-self /\ (0, CFLSend $ "n'" $ "m") \in "Fors")
  }.
  {
    apply DSIfC, DSThin.

    set S := fun ts => {A: ("n'", "m") \in ts}.
    set A := {A: when-on["n"]
      (when-self /\ (0, CFLSend $ "n'" $ "m") \in "Fors")}.
    have HAPerSA := @DPAPerSA C Gamma S "n" A.
    have HNTA : non_temporal_assertion A by repeat constructor.
    specialize (HAPerSA HNTA); clear HNTA.

    have H : Gamma |- C, {A:
      "Fn" = "n" /\
      when-self /\
      S {t: "Fs" $ "n"} /\
      ("Fs'" $ "n", "Fors", "Fois") = periodic C $ "n" $ ("Fs" $ "n") ->
      A
    }.
    rewrite /S /A.
    apply DSIfC.
    do 3 apply DSAndP, DSExchange.
    eapply DAEvaluateP; first by [].
    do 2 apply DAInjectivePairP.
    apply DSAndC; [| apply DSAndC].
    - by apply DAnyAxiom.
    - by apply DAnyAxiom.
    - by apply DASubstituteC; eapply DInMap; first by do 3 apply DSThin.

    rewrite /S in HAPerSA.
    by apply DModusPonensC in HAPerSA; last by []; last by apply DAnyAxiom.
  }

  (* From H4 and H5 *)
  have H6 : Gamma |- C, {A:
    when-on["n"] when[]-> CSLSend $ "n'" $ "m" =>>
    always^ eventually when-on["n"]
      (when-self /\ (0, CFLSend $ "n'" $ "m") \in "Fors")
  }.
  {
    apply DModusPonensC in H5; last by apply DSAxiom.
    eapply DARewriteEntailsC' in H4; last (by apply H5);
      rewrite /rewrite_assertion_pos /= in H4.
    by eapply DARewriteCongruentCR;
      first by apply (DTL119 _ _ {A:
        eventually when-on["n"]
          (when-self /\ (0, CFLSend $ "n'" $ "m") \in "Fors")
        }).
  }

  (* From rule OR *)
  (* NOTE: send_fl(n, m) should be send_fl(n', m) *)
  have H7 : Gamma |- C, {A:
    when-on["n"] (when-self /\ (0, CFLSend $ "n'" $ "m") \in "Fors") =>>
    eventually^ when-on["n"] when[0]-> CFLSend $ "n'" $ "m"
  } by apply (DPOR _ _ "n" 0 {t: CFLSend $ "n'" $ "m"}).

  (* From (6) and (7) *)
  (* NOTE: send_fl(n, m) should be send_fl(n', m) *)
  have H8 : Gamma |- C, {A:
    when-on["n"] when[]-> CSLSend $ "n'" $ "m" =>>
    always^ eventually eventually^ when-on["n"] when[0]-> CFLSend $ "n'" $ "m"
  }.
  {
    by eapply DARewriteEntailsC' in H6; last (by apply H7).
  }

  (* From lemma 120 on (8) *)
  (* NOTE: Lemma 84 does not apply here; must use new lemma 120 instead *)
  have H9 : Gamma |- C, {A:
    when-on["n"] when[]-> CSLSend $ "n'" $ "m" =>>
      always^ eventually^ when-on["n"] when[0]-> CFLSend $ "n'" $ "m"
  }.
  {
    by eapply DARewriteEntailsC' in H8;
      last by apply (DTL120_3 _ _ {A:
        when-on["n"] when[0]-> CFLSend $ "n'" $ "m"}).
  }

  (* By rule FLoss on (1) and (9) *)
  have H10 : Gamma |- C, {A:
    when-on["n"] when[]-> CSLSend $ "n'" $ "m" =>>
    always^ eventually^ when-on["n'"] when[0]<- CFLDeliver $ "n" $ "m"
  }.
  {
    have HFLoss := DPFLoss C Gamma "n" "n'" "m" 0;
      apply DModusPonensC in HFLoss; last by apply DAnyAxiom.
    by eapply DARewriteIfC' in H9; last by apply HFLoss.
  }

  (* From rule IIOI *)
  have H11 : Gamma |- C, {A:
    when-on["n'"] when[0]<- CFLDeliver $ "n" $ "m" =>>
    eventually^ when-on["n'"] when[]<- CSLDeliver $ "n" $ "m"
  }.
  {
    have HIIOI := @DPIIOI C Gamma (fun _ => ATrue)
      "n'" 0 {t: CFLDeliver $ "n" $ "m"} {t: CSLDeliver $ "n" $ "m"}.
    have H' : Gamma |- C, {A:
      ATrue /\
      CSLDeliver $ "n" $ "m" \in
        {t: let: (%, %, #) :=
          indication C $ "n'" $ "s" $ (0, CFLDeliver $ "n" $ "m")
        in: P 0 0}}.
    apply DSAndC; first by apply DSNotC.
    eapply DAEvaluateC; first by []; last by eapply DAPIn.
    specialize (HIIOI H'); clear H'.

    eapply DARewriteIffCR; first by eapply DAndElimination.
    by instantiate
      (1 := {A: when-on[ "n'"] when[ 0 ]<- CFLDeliver $ "n" $ "m"}).
  }

  (* From (10) and (11) *)
  have H12 : Gamma |- C, {A:
    when-on["n"] when[]-> CSLSend $ "n'" $ "m" =>>
    always^ eventually^ eventually^
      when-on["n'"] when[]<- CSLDeliver $ "n" $ "m"
  }.
  {
    by eapply DARewriteEntailsC' in H10; last by apply H11.
  }

  (* From lemma 84 and (12) *)
  (* NOTE: Lemma 84 does not apply here; must use new lemma 120 instead *)
  have H13 : Gamma |- C, {A:
    when-on["n"] when[]-> CSLSend $ "n'" $ "m" =>>
    always^ eventually^
      when-on["n'"] when[]<- CSLDeliver $ "n" $ "m"
  }.
  {
    by eapply DARewriteEntailsC' in H12;
      last by apply (DTL120_2 _ _ {A:
        when-on["n'"] when[]<- CSLDeliver $ "n" $ "m"}).
  }

  eapply DARewriteIfC' in H13;
    last by apply DTL121 with
      (A := {A: when-on["n'"] when[]<- CSLDeliver $ "n" $ "m"}).
  eapply DARewriteIfC' in H13;
    last by apply DTL122 with
      (A := {A: when-on["n'"] when[]<- CSLDeliver $ "n" $ "m"}).

  by [].
Qed.

(* No-forge
 * If a node n delivers a emssage m with sender n', then m was
 * previously sent to n by n' *)
Theorem SL_2 : [::] |- stubborn_link, {A:
  when-on["n"] when[]<- {t: CSLDeliver $ "n'" $ "m"} <~
  when-on["n'"] when[]-> {t: CSLSend $ "n" $ "m"}
}.
Proof.
  pose Gamma : context := [::]; rewrite -/Gamma.
  pose C := stubborn_link; rewrite -/C.

  (* By rule OI' *)
  have H1 : Gamma |- C, {A:
    when-on["n"] when[]<- CSLDeliver $ "n'" $ "m" =>>
    eventuallyp when-on["n"] (CSLDeliver $ "n'" $ "m" \in "Fois" /\ when-self)
  }.
  {
    (* Instantiate OI' *)
    have HOI' := DPOI' C Gamma "n" {t: CSLDeliver $ "n'" $ "m"}.
    by eapply DARewriteIfC' in HOI';
      last by apply DTL123 with
        (A := {A: when-on["n"] (CSLDeliver $ "n'" $ "m" \in "Fois" /\
          when-self)}).
  }

  (* By rule InvL *)
  have H2 : Gamma |- C, {A:
    when-on["n"] (CSLDeliver $ "n'" $ "m" \in "Fois" /\ when-self) =>>
    when-on["n"] when[0]<- CFLDeliver $ "n'" $ "m"
  }.
  {
    (* Instantiate InvL *)
    set A := {A:
      when-on["n"] (CSLDeliver $ "n" $ "m" \in "Fois") ->
      when-on["n"] when[0]<- CFLDeliver $ "n'" $ "m"
    }. (* TODO: Confirm that this is the right A *)
    have HInvL := @DPInvL C Gamma A.

    (* Prove that A is non-temporal *)
    have HNTA : non_temporal_assertion A by repeat constructor.
    specialize (HInvL HNTA); clear HNTA.

    (* Prove that A holds for requests *)
    have HInvLr : Gamma |- C, {A:
      forall: "e",
      when[]-> "e" /\
      request C $ "Fn" $ ("Fs" $ "Fn") $ "e" =
        ("Fs'" $ "Fn", "Fors", "Fois") ->
      A
    }.
    {
      admit. (* TODO *)
    }
    specialize (HInvL HInvLr); clear HInvLr.

    (* Prove that A holds for indications *)
    have HInvLi : Gamma |- C, {A:
      forall: "i", forall: "e",
      when["i"]<- "e" /\
      indication C $ "Fn" $ ("Fs" $ "Fn") $ ("i", "e") =
        ("Fs'" $ "Fn", "Fors", "Fois") ->
      A
    }.
    {
      admit. (* TODO *)
    }
    specialize (HInvL HInvLi); clear HInvLi.

    (* Prove that A holds for periodics *)
    have HInvLp : Gamma |- C, {A:
      when[]~> PE /\
      periodic C $ "Fn" $ ("Fs" $ "Fn") = ("Fs'" $ "Fn", "Fors", "Fois") ->
      A
    }.
    {
      admit. (* TODO *)
    }
    specialize (HInvL HInvLp); clear HInvLp.

    (* Now what? *)
    admit. (* TODO *)
  }

  (* From (1) and (2) *)
  have H3 : Gamma |- C, {A:
    when-on["n"] when[]<- CSLDeliver $ "n'" $ "m" <~
    when-on["n"] when[0]<- CFLDeliver $ "n'" $ "m"
  }.
  {
    by eapply DARewriteEntailsC' in H1; last by apply H2.
  }

  (* By rule NForge *)
  have H4 : Gamma |- C, {A:
    when-on["n"] when[0]<- CFLDeliver $ "n'" $ "m" <~
    when-on["n'"] when[0]-> CFLSend $ "n" $ "m"
  }.
  {
    (* Instantiate NForge *)
    by apply (DPNForge C Gamma "n'" "n" "m" 0).
  }

  (* By lemma 85 on (3) and (4) *)
  have H5 : Gamma |- C, {A:
    when-on["n"] when[]<- CSLDeliver $ "n'" $ "m" <~
    when-on["n'"] when[0]-> CFLSend $ "n" $ "m"
  }.
  {
    by apply (DTL85 H3 H4).
  }

  (* By rule OR' *)
  have H6 : Gamma |- C, {A:
    when-on["n'"] when[0]-> CFLSend $ "n" $ "m" =>>
    eventuallyp when-on["n'"]
      ((0, CFLSend $ "n" $ "m") \in "Fors" /\ when-self)
  }.
  {
    (* Instantiate OR' *)
    have HOR' := DPOR' C Gamma "n'" 0 {t: CFLSend $ "n" $ "m"}.
    by eapply DARewriteIfC' in HOR';
      last by apply DTL123 with
        (A := {A: when-on["n'"] ((0, CFLSend $ "n" $ "m") \in "Fors" /\
          when-self)}).
  }

  (* By rule InvL *)
  have H7 : Gamma |- C, {A:
    when-on["n'"] ((0, CFLSend $ "n" $ "m") \in "Fors" /\ when-self) =>>
    when-on["n'"] when[]-> CSLSend $ "n" $ "m"
  }.
  {
    admit. (* TODO *)
  }

  (* From (6) and (7) *)
  have H8 : Gamma |- C, {A:
    when-on["n'"] when[0]-> CFLSend $ "n" $ "m" <~
    when-on["n'"] when[]-> CSLSend $ "n" $ "m"
  }.
  {
    by eapply DARewriteEntailsC' in H6; last by apply H7.
  }

  (* From (5) and (8) *)
  have H9 : Gamma |- C, {A:
    when-on["n"] when[]<- CSLDeliver $ "n'" $ "m" <~
    eventuallyp when-on["n'"] when[]-> CSLSend $ "n" $ "m"
  }.
  {
    by eapply DARewriteEntailsC' in H5; last by apply H8.
  }

  (* Line missing from paper proof: *)
  (* By lemma 83 on (9) *)
  have H10 : Gamma |- C, {A:
    when-on["n"] when[]<- CSLDeliver $ "n'" $ "m" <~
    when-on["n'"] when[]-> CSLSend $ "n" $ "m"
  }.
  {
    by eapply DARewriteCongruentCL;
      first by apply DTL83_1 with
      (A := {A: when-on["n'"] when[]-> CSLSend $ "n" $ "m"}).
  }

  by [].
Admitted. (* TODO *)
