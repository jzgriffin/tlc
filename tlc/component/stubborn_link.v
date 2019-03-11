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
Require Import tlc.utility.partial_map.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Functional implementation *)
Definition stubborn_link :=
  let flc := 0 in
  Component
  (* initialize *)
  {t: fun:
    (* Begin scoped parameters *)
    let n := {t: #(0, 0)} in
    (* End scoped parameters *)
    []
  }
  (* request *)
  {t: fun: fun: fun:
    (* Begin scoped parameters *)
    let n := {t: #(2, 0)} in
    let s := {t: #(1, 0)} in
    let ir := {t: #(0, 0)} in
    (* End scoped parameters *)
    match: ir with: CSLSend $ # $ # (* n', m *)
    then:
      (* Begin scoped parameters *)
      let n := {t: #(3, 0)} in
      let s := {t: #(2, 0)} in
      let ir := {t: #(1, 0)} in
      let n' := {t: #(0, 0)} in
      let m := {t: #(0, 1)} in
      (* End scoped parameters *)
      (s \union [(n', m)], [(flc, CFLSend $ n' $ m)], [])
    else: TFailure
  }
  (* indication *)
  {t: fun: fun: fun:
    (* Begin scoped parameters *)
    let n' := {t: #(2, 0)} in
    let s := {t: #(1, 0)} in
    let ii := {t: #(0, 0)} in
    (* End scoped parameters *)
    match: ii with: (flc, CFLDeliver $ # $ #) (* n, m *)
    then:
      (* Begin scoped parameters *)
      let n' := {t: #(3, 0)} in
      let s := {t: #(2, 0)} in
      let ii := {t: #(1, 0)} in
      let n := {t: #(0, 0)} in
      let m := {t: #(0, 1)} in
      (* End scoped parameters *)
      (s, [], [CSLDeliver $ n $ m])
    else: TFailure
  }
  (* periodic *)
  {t: fun: fun:
    (* Begin scoped parameters *)
    let n' := {t: #(1, 0)} in
    let s := {t: #(0, 0)} in
    (* End scoped parameters *)
    (s, (fun: let: (#, #) := #0 in: (flc, CFLSend $ #0 $ #1)) <$> s, [])
  }.

(* Specification *)

(* Stubborn delivery
 * If a correct node n sends a message m to a correct node n', then n'
 * delivers m infinitely often *)
Theorem SL_1 : Context [::] [::] |- stubborn_link, {A:
  forall: "n", "n'", "m":
  correct "n" /\ correct "n'" ->
  when-on["n"] when[]-> CSLSend $ "n'" $ "m" =>>
  always eventually when-on["n'"] when[]<- CSLDeliver $ "n" $ "m"
}.
Proof.
  (* Introduce context *)
  set C := stubborn_link; rewrite -/C.
  d_forallc "n"; d_forallc "n'"; d_forallc "m"; d_ifc; d_splitp.

  (* By IR *)
  d_have {A:
    when-on["n"] when[]-> CSLSend $ "n'" $ "m" =>>
    when-self /\ ("n'", "m") \in ("Fs'" $ "n")
  }.
  {
    (* Instantiate IR *)
    eapply DSCut; first by apply DPIR.
    d_forallp {t: CSLSend $ "n'" $ "m"}; d_evalp.

    admit. (* TODO *)
  }

  (* By InvS'' *)
  d_have {A:
    when-self /\ ("n'", "m") \in ("Fs'" $ "n") =>>
    always^ (when-self -> ("n'", "m") \in ("Fs" $ "n"))
  }.
  {
    (* Instantiate InvS'' *)
    set S := fun ts => {A: ("n'", "m") \in ts}.
    eapply DSCut; first by apply DPInvS'' with (S := S).
    d_forallp "n".

    (* Prove property for requests *)
    d_ifp.
      d_forallc "s"; d_forallc "e"; d_ifc.
      eapply DARewriteIffPL.
        eapply DSCut; first by apply DAPConcatIn.
        by d_forallp {t: ("n'", "m")}; d_forallp "s".
      rewrite /rewrite_assertion_any /=.

      d_existsp "sl"; d_existsp "sr".
      (*
      apply DASubstituteC; eapply DAEvaluateC; first by [].
      by apply DInUnion, DSOrCL, DInConcat, DSOrCR, DInConcat, DSOrCL;
        eapply DAPIn.
      *)
      admit.

    (* Prove property for indications *)
    d_ifp.
      d_forallc "s"; d_forallc "i"; d_forallc "e"; d_ifc.
      (*
      d_evalc.
      *)
      admit.

    (* Prove property for periodics *)
    d_ifp.
      by d_forallc "s"; d_ifc; d_evalc.

    by [].
  }

  (* From (2) and (3) *)
  d_have {A:
    when-on["n"] when[]-> CSLSend $ "n'" $ "m" =>>
    always^ (when-self -> ("n'", "m") \in ("Fs" $ "n"))
  }.
  {
    d_rotate 1; eapply DARewriteEntailsP; first by d_rotate 2; apply DSAxiom.
    by rewrite /rewrite_assertion_pos /=.
  }

  (* By APerSA *)
  d_have {A:
    correct "n" -> (when-self -> ("n'", "m") \in ("Fs" $ "n")) =>>
    always eventually when-on["n"]
      (when-self /\ (0, CFLSend $ "n'" $ "m") \in "Fors")
  }.
  {
    d_ifc; d_clear.

    (* Instantiate APerSA *)
    set S := fun ts => {A: ("n'", "m") \in ts}.
    set A := {A: when-on["n"]
      (when-self /\ (0, CFLSend $ "n'" $ "m") \in "Fors")}.
    eapply DSCut; first by apply DPAPerSA with (S := S) (A := A);
      first by repeat constructor.
    d_forallp "n".

    d_ifp.
      d_ifc; do 3 (d_splitp; d_swap).
      d_evalp; do 2 apply DAInjectivePairP.
      d_splitc; first by d_assumption.
      d_splitc; first by d_assumption.
      by d_substc; eapply DAPInMap; first by do 3 d_clear.

    by d_ifp; first by d_assumption.
  }

  (* From (4) and (5) *)
  d_have {A:
    when-on["n"] when[]-> CSLSend $ "n'" $ "m" =>>
    always^ eventually when-on["n"]
      (when-self /\ (0, CFLSend $ "n'" $ "m") \in "Fors")
  }.
  {
    d_ifp; first by d_assumption.
    d_rotate 1; eapply DARewriteEntailsP; first by d_rotate 4; apply DSAxiom.
    rewrite /rewrite_assertion_pos /=.
    by eapply DARewriteCongruentCR; first by eapply DTL119 with (A := {A:
      eventually when-on["n"]
        (when-self /\ (0, CFLSend $ "n'" $ "m") \in "Fors")
      }).
  }

  (* From OR *)
  (* NOTE: send_fl(n, m) should be send_fl(n', m) *)
  d_have {A:
    when-on["n"] (when-self /\ (0, CFLSend $ "n'" $ "m") \in "Fors") =>>
    eventually^ when-on["n"] when[0]-> CFLSend $ "n'" $ "m"
  }.
  {
    (* Instantiate OR *)
    eapply DSCut; first by apply DPOR.
    by d_forallp "n"; d_forallp 0; d_forallp {t: CFLSend $ "n'" $ "m"}.
  }

  (* From (6) and (7) *)
  (* NOTE: send_fl(n, m) should be send_fl(n', m) *)
  d_have {A:
    when-on["n"] when[]-> CSLSend $ "n'" $ "m" =>>
    always^ eventually eventually^ when-on["n"] when[0]-> CFLSend $ "n'" $ "m"
  }.
  {
    by d_rotate 1; eapply DARewriteEntailsP;
      first by d_rotate 6; apply DSAxiom.
  }

  (* From lemma 120 on (8) *)
  (* NOTE: Lemma 84 does not apply here; must use new lemma 120 instead *)
  d_have {A:
    when-on["n"] when[]-> CSLSend $ "n'" $ "m" =>>
      always^ eventually^ when-on["n"] when[0]-> CFLSend $ "n'" $ "m"
  }.
  {
    by eapply DARewriteEntailsP; first by eapply DTL120_3 with (A := {A:
      when-on["n"] when[0]-> CFLSend $ "n'" $ "m"}).
  }

  (* By rule FLoss on (1) and (9) *)
  d_have {A:
    when-on["n"] when[]-> CSLSend $ "n'" $ "m" =>>
    always^ eventually^ when-on["n'"] when[0]<- CFLDeliver $ "n" $ "m"
  }.
  {
    (* Instantiate FLoss *)
    eapply DSCut; first by apply DPFLoss with
      (tn := "n") (tn' := "n'") (tm := "m") (ti := 0).
    d_ifp; first by d_assumption.

    by d_rotate 1; eapply DARewriteIfP;
      first by by d_rotate 9; apply DSAxiom.
  }

  (* From rule IIOI *)
  d_have {A:
    when-on["n'"] when[0]<- CFLDeliver $ "n" $ "m" =>>
    eventually^ when-on["n'"] when[]<- CSLDeliver $ "n" $ "m"
  }.
  {
    (* Instantiate IIOI *)
    eapply DSCut; first by apply DPIIOI with (S := fun _ => ATrue).
    d_forallp "n'"; d_forallp 0; d_forallp {t: CFLDeliver $ "n" $ "m"};
      d_forallp {t: CSLDeliver $ "n" $ "m"}.
    d_ifp.
      d_forallc "s"; d_splitc; first by d_notc.
      by d_evalc; eapply DAPIn.

    by eapply DARewriteIffCR; first by eapply DSAndElimination with (A :=
      {A: when-on[ "n'"] when[ 0 ]<- CFLDeliver $ "n" $ "m"}).
  }

  (* From (10) and (11) *)
  d_have {A:
    when-on["n"] when[]-> CSLSend $ "n'" $ "m" =>>
    always^ eventually^ eventually^
      when-on["n'"] when[]<- CSLDeliver $ "n" $ "m"
  }.
  {
    by d_rotate 1; eapply DARewriteEntailsP;
      first by d_rotate 10; apply DSAxiom.
  }

  (* From lemma 84 and (12) *)
  (* NOTE: Lemma 84 does not apply here; must use new lemma 120 instead *)
  d_have {A:
    when-on["n"] when[]-> CSLSend $ "n'" $ "m" =>>
    always^ eventually^
      when-on["n'"] when[]<- CSLDeliver $ "n" $ "m"
  }.
  {
    by eapply DARewriteEntailsP; first by eapply DTL120_2 with (A := {A:
      when-on["n'"] when[]<- CSLDeliver $ "n" $ "m"}).
  }

  eapply DARewriteIfP; first by eapply DTL121 with (A := {A:
    when-on["n'"] when[]<- CSLDeliver $ "n" $ "m"}).
  eapply DARewriteIfP; first by eapply DTL122 with (A := {A:
    when-on["n'"] when[]<- CSLDeliver $ "n" $ "m"}).

  by [].
Admitted. (* TODO *)

(* No-forge
 * If a node n delivers a message m with sender n', then m was previously sent
 * to n by n' *)
Theorem SL_2 : Context [::] [::] |- stubborn_link, {A:
  when-on["n"] when[]<- {t: CSLDeliver $ "n'" $ "m"} <~
  when-on["n'"] when[]-> {t: CSLSend $ "n" $ "m"}
}.
Proof.
  pose C := stubborn_link; rewrite -/C.

  (* By OI' *)
  d_have {A:
    when-on["n"] when[]<- CSLDeliver $ "n'" $ "m" =>>
    eventuallyp (when-on["n"] (CSLDeliver $ "n'" $ "m" \in "Fois") /\
      when-self)
  }.
  {
    (* Instantiate OI' *)
    eapply DSCut; first by apply DPOI'.
    d_forallp "n"; d_forallp {t: CSLDeliver $ "n'" $ "m"}.

    by eapply DARewriteIfP; first by apply DTL123 with (A := {A:
      when-on["n"] (CSLDeliver $ "n'" $ "m" \in "Fois") /\ when-self}).
  }

  (* By InvL *)
  d_have {A:
    when-on["n"] (CSLDeliver $ "n'" $ "m" \in "Fois") /\ when-self =>>
    when-on["n"] when[0]<- CFLDeliver $ "n'" $ "m"
  }.
  {
    (* Instantiate InvL *)
    set A := {A:
      when-on["n"] (CSLDeliver $ "n'" $ "m" \in "Fois") ->
      when-on["n"] when[0]<- CFLDeliver $ "n'" $ "m"
    }.
    eapply DSCut; first by apply DPInvL with (A := A);
      first by repeat constructor.

    (* Prove that A holds for requests *)
    d_ifp.
      d_forallc "e".
      admit. (* TODO *)

    (* Prove that A holds for indications *)
    d_ifp.
      d_forallc "i"; d_forallc "e".
      admit. (* TODO *)

    (* Prove that A holds for periodics *)
    d_ifp.
      admit. (* TODO *)

    rewrite /A.
    eapply DARewriteIffPL; first by apply DSMergeIf with
      (Ap1 := {A: when-self})
      (Ap2 := {A: when-on["n"] (CSLDeliver $ "n'" $ "m" \in "Fois")})
      (Ac := {A: when-on["n"] when[0]<- CFLDeliver $ "n'" $ "m"}).
    by eapply DARewriteIffPL; first by apply DSAndCommutative with
      (Acl := {A: when-self})
      (Acr := {A: when-on["n"] (CSLDeliver $ "n'" $ "m" \in "Fois")}).
  }

  (* From (1) and (2) *)
  d_have {A:
    when-on["n"] when[]<- CSLDeliver $ "n'" $ "m" <~
    when-on["n"] when[0]<- CFLDeliver $ "n'" $ "m"
  }.
  {
    by d_rotate 1; eapply DARewriteEntailsP; first by exact: DSAxiom.
  }

  (* By NForge *)
  d_have {A:
    when-on["n"] when[0]<- CFLDeliver $ "n'" $ "m" <~
    when-on["n'"] when[0]-> CFLSend $ "n" $ "m"
  }.
  {
    (* Instantiate NForge *)
    by apply (DPNForge _ _ "n'" "n" "m" 0).
  }

  (* By lemma 85 on (3) and (4) *)
  d_have {A:
    when-on["n"] when[]<- CSLDeliver $ "n'" $ "m" <~
    when-on["n'"] when[0]-> CFLSend $ "n" $ "m"
  }.
  {
    eapply DTL85.
    - by d_rotate 1.
    - by [].
  }

  (* By OR' *)
  d_have {A:
    when-on["n'"] when[0]-> CFLSend $ "n" $ "m" =>>
    eventuallyp (when-on["n'"]
      ((0, CFLSend $ "n" $ "m") \in "Fors") /\ when-self)
  }.
  {
    (* Instantiate OR' *)
    eapply DSCut; first by apply DPOR'.
    d_forallp "n'"; d_forallp 0; d_forallp {t: CFLSend $ "n" $ "m"}.

    by eapply DARewriteIfP; first by apply DTL123 with
        (A := {A: (when-on["n'"] ((0, CFLSend $ "n" $ "m") \in "Fors")) /\
          when-self}).
  }

  (* By InvL *)
  d_have {A:
    when-on["n'"] ((0, CFLSend $ "n" $ "m") \in "Fors") /\ when-self =>>
    when-on["n'"] when[]-> CSLSend $ "n" $ "m"
  }.
  {
    (* Instantiate InvL *)
    set A := {A:
      when-on["n'"] ((0, CFLSend $ "n" $ "m") \in "Fors") ->
      when-on["n'"] when[]-> CSLSend $ "n" $ "m"
    }.
    eapply DSCut; first by apply DPInvL with (A := A);
      first by repeat constructor.

    (* Prove that A holds for requests *)
    d_ifp.
      d_forallc "e".
      admit. (* TODO *)

    (* Prove that A holds for indications *)
    d_ifp.
      d_forallc "i"; d_forallc "e".
      admit. (* TODO *)

    (* Prove that A holds for periodics *)
    d_ifp.
      admit. (* TODO *)

    rewrite /A.
    eapply DARewriteIffPL; first by apply DSMergeIf with
      (Ap1 := {A: when-self})
      (Ap2 := {A: when-on["n'"] ((0, CFLSend $ "n" $ "m") \in "Fors")})
      (Ac := {A: when-on["n'"] when[]-> CSLSend $ "n" $ "m"}).
    by eapply DARewriteIffPL; first by apply DSAndCommutative with
      (Acl := {A: when-self})
      (Acr := {A: when-on["n'"] ((0, CFLSend $ "n" $ "m") \in "Fors")}).
  }

  (* From (6) and (7) *)
  d_have {A:
    when-on["n'"] when[0]-> CFLSend $ "n" $ "m" <~
    when-on["n'"] when[]-> CSLSend $ "n" $ "m"
  }.
  {
    by d_rotate 1; eapply DARewriteEntailsP;
      first by d_rotate 5; exact: DSAxiom.
  }

  (* From (5) and (8) *)
  d_have {A:
    when-on["n"] when[]<- CSLDeliver $ "n'" $ "m" <~
    eventuallyp when-on["n'"] when[]-> CSLSend $ "n" $ "m"
  }.
  {
    by d_rotate 3; eapply DARewriteEntailsP;
      first by d_rotate 4; exact: DSAxiom.
  }

  (* By lemma 83 on (9) *)
  (* NOTE: This line is missing from the paper proof *)
  d_have {A:
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
