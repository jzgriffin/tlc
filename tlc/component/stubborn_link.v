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
  always^ eventually^ when-on["n'"] when[]<- CSLDeliver $ "n" $ "m"
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
    always^ (when-self -> ("n'", "m") \in ("Fs'" $ "n"))
  }.
  {
    (*apply InvS'' with (S := {t: fun: (tn', tm) \in (#0 $ tn)}).*)
    admit. (* TODO *)
  }

  (* From H2 and H3 *)
  have H4 : Gamma |- C, {A:
    when-on["n"] when[]-> CSLSend $ "n'" $ "m" =>>
    always^ (when-self -> ("n'", "m") \in ("Fs'" $ "n"))
  }.
  {
    by eapply DARewriteEntailsC' in H2; last (by apply H3).
  }

  (* By rule APerSA *)
  have H5 : Gamma |- C, {A:
    correct "n" -> (when-self -> ("n'", "m") \in ("Fs'" $ "n")) =>>
    always eventually when-on["n"]
      (when-self /\ (0, CFLSend $ "n'" $ "m") \in "Fors")
  }.
  {
    admit. (* TODO *)
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
    admit.
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

  by [].
Admitted. (* TODO *)

(* No-forge
 * If a node n delivers a emssage m with sender n', then m was
 * previously sent to n by n' *)
Theorem SL_2 : [::] |- stubborn_link, {A:
  forall: "n", forall: "n'", forall: "m",
  (when-on["n"] when[]<- {t: CSLDeliver $ "n'" $ "m"}) <~
  (when-on["n'"] when[]-> {t: CSLSend $ "n" $ "m"})
}.
Proof.
Admitted. (* TODO *)
