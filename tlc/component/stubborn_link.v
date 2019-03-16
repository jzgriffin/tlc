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
    match: ir with:
    {{ CSLSend $ # $ # (* n', m *) ->
      (* Begin scoped parameters *)
      let n := {t: #(3, 0)} in
      let s := {t: #(2, 0)} in
      let ir := {t: #(1, 0)} in
      let n' := {t: #(0, 0)} in
      let m := {t: #(0, 1)} in
      (* End scoped parameters *)
      (s \union [(n', m)], [(flc, CFLSend $ n' $ m)], [])
    }}
  }
  (* indication *)
  {t: fun: fun: fun:
    (* Begin scoped parameters *)
    let n' := {t: #(2, 0)} in
    let s := {t: #(1, 0)} in
    let ii := {t: #(0, 0)} in
    (* End scoped parameters *)
    match: ii with:
    {{ (flc, CFLDeliver $ # $ #) (* n, m *) ->
      (* Begin scoped parameters *)
      let n' := {t: #(3, 0)} in
      let s := {t: #(2, 0)} in
      let ii := {t: #(1, 0)} in
      let n := {t: #(0, 0)} in
      let m := {t: #(0, 1)} in
      (* End scoped parameters *)
      (s, [], [CSLDeliver $ n $ m])
    }}
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

    set t1l := {t: "Fs'" $ "Fn"}.
      set t2l := {t: "Fors"};
      set t3l := {t: "Fois"};
      set t1r := {t: ("Fs" $ "Fn") \union [("n'", "m")]};
      set t2r := {t: [(0, CFLSend $ "n'" $ "m")]};
      set t3r := {t: []};
      d_destructpairp {t: (t1l, t2l)} t3l {t: (t1r, t2r)} t3r;
      d_destructpairp t1l t2l t1r t2r;
      rewrite_assertion_any;
      rewrite /t1l /t2l /t3l /t1r /t2r /t3r;
      clear t1l t2l t3l t1r t2r t3r.

    d_have {A: ("Fs'" $ "Fn" = "Fs" $ "Fn" \union [("n'", "m")] /\
      "Fors" = [(0, CFLSend $ "n'" $ "m")]) /\ "Fois" = [] ->
      ("n'", "m") \in "Fs'" $ "Fn"}.
      d_ifc; d_splitp; d_splitp; d_substc.
      eapply DSCut; first by eapply DAPInUnion.
      d_forallp {t: "Fs" $ "Fn"};
        d_forallp {t: [("n'", "m")]};
        d_forallp {t: ("n'", "m")}.
      by d_ifp; first by by d_right; eapply DAPIn.
    d_swap; eapply DARewriteIfP; first by d_head. rewrite_assertion_pos.

    eapply DSCut.
      apply DSIfAndSplit with
        (Ap := {A: when[]-> CSLSend $ "n'" $ "m"})
        (Acl := {A: when-self})
        (Acr := {A: ("n'", "m") \in "Fs'" $ "Fn"}).
      d_splitp; d_swap; d_clear; d_ifp.
      d_splitc.
      - eapply DSCut; first by apply DPWhenTopRequestSelf.
        by d_forallp {t: CSLSend $ "n'" $ "m"}; d_splitp.
      - by d_splitp.

    do 4 (d_swap; d_clear). (* Clean up the context *)
    d_have {A: when-on["n"] when[]-> CSLSend $ "n'" $ "m" -> when-self /\
      ("n'", "m") \in "Fs'" $ "n"}.
      d_ifc; d_splitp; d_rotate 2.
      d_ifp; first by d_swap.
      by d_subst.

    by d_have {A: when-on["n"] when[]-> CSLSend $ "n'" $ "m" =>> when-self /\
      ("n'", "m") \in "Fs'" $ "n"}; first by apply DTGeneralization.
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
      rewrite_assertion_any.

      d_existsp "sl"; d_existsp "sr"; d_evalc.
      d_destructc (fun t => {A: ("n'", "m") \in
        match: t with: {{(#, %, %) -> #0}}}).
      d_forallc "?n"; d_forallc "?m".
      d_ifc; d_substc; d_evalc.

      eapply DSCut; first by apply DAPInUnion.
      d_forallp {t: "sl" ++ [("n'", "m")] ++ "sr"};
        d_forallp {t: [("?m", "?n")]};
        d_forallp {t: ("n'", "m")}.
      d_ifp.
        d_left.
        eapply DSCut; first by apply DAPInConcat.
        d_forallp {t: "sl"};
          d_forallp {t: [("n'", "m")] ++ "sr"};
          d_forallp {t: ("n'", "m")}.
        d_ifp.
          d_right.
          eapply DSCut; first by apply DAPInConcat.
          d_forallp {t: [("n'", "m")]};
            d_forallp {t: "sr"};
            d_forallp {t: ("n'", "m")}.
          d_ifp; first by d_left; by eapply DAPIn.
          d_head.
        d_head.

      d_head.

    (* Prove property for indications *)
    d_ifp.
      d_forallc "s"; d_forallc "i"; d_forallc "e"; d_ifc; d_evalc.
      d_destructc (fun t => {A: ("n'", "m") \in
        match: t with: {{(#, %, %) -> #0}}}).
      d_forallc "?n"; d_forallc "?m".
      by d_ifc; d_substc; d_evalc; d_clear.

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
    by d_rotate 1; eapply DARewriteEntailsP;
      first by d_rotate 2; d_head.
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
      d_evalp.
      set tf := {t: fun: match: #0 with:
        {{(#, #) -> CPair $ 0 $ (CFLSend $ #0 $ #1)}}};
        set t1l := {t: "Fs'" $ "n"};
        set t2l := {t: "Fors"};
        set t3l := {t: "Fois"};
        set t1r := {t: ("Fs" $ "n")};
        set t2r := {t: FMap $ tf $ t1r};
        set t3r := {t: []};
        d_destructpairp {t: (t1l, t2l)} t3l {t: (t1r, t2r)} t3r;
        d_destructpairp t1l t2l t1r t2r;
        rewrite_assertion_any;
        rewrite /t1l /t2l /t3l /t1r /t2r /t3r /t1r;
        clear t1l t2l t3l t1r t2r t3r;
        do 2 d_splitp.

      d_splitc; first by d_assumption.
      d_splitc; first by d_assumption.
      d_substc.
      eapply DSCut; first by apply DAPInMap.
      d_forallp tf; d_forallp {t: ("n'", "m")};
        d_forallp {t: "Fs" $ "n"}.
      d_splitp; d_swap; d_clear; d_ifp; first by d_rotate 3; d_head.
      by d_evalp.

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
    d_rotate 1; eapply DARewriteEntailsP; first by d_rotate 4; d_head.
    rewrite_assertion_pos.
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
      first by d_rotate 6; d_head.
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
      first by by d_rotate 9; d_head.
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
      first by d_rotate 10; d_head.
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
Qed.

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
    d_clear. (* Clean up the context *)

    (* Instantiate InvL *)
    eapply DSCut; first by apply DPInvL with (A := {A:
        when-on["n"] (CSLDeliver $ "n'" $ "m" \in "Fois") ->
        when-on["n"] when[0]<- CFLDeliver $ "n'" $ "m"
      }); first by repeat constructor.

    (* Prove for requests *)
    d_ifp.
      (* Obtain the first contradictory premise *)
      d_forallc "e".
      d_ifc; d_splitp; d_swap; d_evalp.
      d_destructp (fun t => {A: ("Fs'" $ "Fn", "Fors", "Fois") = t}).
      d_forallp "m"; d_forallp "n'"; d_splitp; d_swap.
      d_substp; d_evalp.
      set t1l := {t: "Fs'" $ "Fn"};
        set t2l := {t: "Fors"};
        set t3l := {t: "Fois"};
        set t1r := {t: ("Fs" $ "Fn") \union [("n'", "m")]};
        set t2r := {t: [(0, CFLSend $ "n'" $ "m")]};
        set t3r := {t: []};
        d_destructpairp {t: (t1l, t2l)} t3l {t: (t1r, t2r)} t3r;
        d_destructpairp t1l t2l t1r t2r;
        rewrite_assertion_any;
        rewrite /t1l /t2l /t3l /t1r /t2r /t3r /t1r;
        clear t1l t2l t3l t1r t2r t3r;
        do 2 d_splitp.
      do 2 d_clear; do 2 (d_swap; d_clear). (* Clean up the context *)

      (* Obtain the second contradictory premise *)
      d_ifc; d_splitp; d_clear; d_substp.

      (* Prove the contradiction *)
      eapply DSCut; first by eapply DAPInNil.
      d_forallp {t: CSLDeliver $ "n'" $ "m"}.
      eapply DSCut; first by eapply DSNotImpliesFalse with (Ac := {A:
        CSLDeliver $ "n'" $ "m" \in CNil}).
      d_swap; eapply DARewriteIffPL; first by d_head.
      rewrite_assertion_any; d_swap; d_clear.
      by d_ifp; first by d_head; d_false.

    (* Prove for indications *)
    d_ifp.
      d_forallc "i"; d_forallc "e".
      d_ifc; d_splitp; d_swap; d_evalp.
      d_destructp (fun t => {A: ("Fs'" $ "Fn", "Fors", "Fois") = t}).
      d_forallp "m"; d_forallp "n'"; d_splitp; d_swap; d_subst; d_evalp.
      set t1l := {t: "Fs'" $ "Fn"};
        set t2l := {t: "Fors"};
        set t3l := {t: "Fois"};
        set t1r := {t: ("Fs" $ "Fn")};
        set t2r := {t: []};
        set t3r := {t: [CSLDeliver $ "n'" $ "m"]};
        d_destructpairp {t: (t1l, t2l)} t3l {t: (t1r, t2r)} t3r;
        d_destructpairp t1l t2l t1r t2r;
        rewrite_assertion_any;
        rewrite /t1l /t2l /t3l /t1r /t2r /t3r /t1r;
        clear t1l t2l t3l t1r t2r t3r;
        do 2 d_splitp.
      d_ifc; d_splitp.
      d_splitc; first by d_head; d_clear.
      d_rotate 5;
        d_destructpairp {t: "i"} {t: "e"} {t: 0} {t: CFLDeliver $ "n'" $ "m"}.
      rewrite_assertion_any; d_splitp.
      d_rotate 2; d_splitp; d_swap; d_splitp.
      do 2 d_substc.
      d_splitc; first by eapply DAPEqual.
      d_splitc; first by eapply DAPEqual.
      by eapply DAPEqual.

    (* Prove for periodics *)
    d_ifp.
      (* Obtain the first contradictory premise *)
      d_ifc; d_splitp; d_swap; d_evalp.
      set t1l := {t: "Fs'" $ "Fn"};
        set t2l := {t: "Fors"};
        set t3l := {t: "Fois"};
        set t1r := {t: ("Fs" $ "Fn")};
        set t2r := {t: FMap $ (fun: match: #0 with: {{
          (#, #) -> CPair $ 0 $ (CFLSend $ #0 $ #1)}}) $ ("Fs" $ "Fn")};
        set t3r := {t: []};
        d_destructpairp {t: (t1l, t2l)} t3l {t: (t1r, t2r)} t3r;
        d_destructpairp t1l t2l t1r t2r;
        rewrite_assertion_any;
        rewrite /t1l /t2l /t3l /t1r /t2r /t3r /t1r;
        clear t1l t2l t3l t1r t2r t3r;
        do 2 d_splitp.
      do 2 d_clear; (d_swap; d_clear). (* Clean up the context *)

      (* Obtain the second contradictory premise *)
      d_ifc; d_splitp; d_clear; d_substp.

      (* Prove the contradiction *)
      eapply DSCut; first by eapply DAPInNil.
      d_forallp {t: CSLDeliver $ "n'" $ "m"}.
      eapply DSCut; first by eapply DSNotImpliesFalse with (Ac := {A:
        CSLDeliver $ "n'" $ "m" \in CNil}).
      d_swap; eapply DARewriteIffPL; first by d_head.
      rewrite_assertion_any; d_swap; d_clear.
      by d_ifp; first by d_head; d_false.

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
    by d_rotate 1; eapply DARewriteEntailsP; first by d_head.
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

  (* By InvSA *)
  d_have {A:
    when-on["n'"] (("n", "m") \in "Fs" $ "n'") /\ when-self =>>
    eventuallyp^ when-on["n'"] when[]-> CSLSend $ "n" $ "m"
  }.
  {
    do 6 d_clear. (* Clean up the context *)

    (* Instantiate InvSA *)
    eapply DSCut; first by apply DPInvSA with
      (S := fun ts => {A: when-on["n'"] (("n", "m") \in ts)})
      (A := {A: when[]-> CSLSend $ "n" $ "m"});
      first by repeat constructor.
    d_forallp "n'".

    (* Prove for initialization *)
    d_ifp.
      d_evalc.
      eapply DSCut; first by eapply DAPInNil.
      d_forallp {t: ("n", "m")}.
      d_notc; d_splitp; d_clear; d_swap.
      eapply DSCut; first by eapply DSNotImpliesFalse with (Ac := {A:
        ("n", "m") \in []}).
      d_swap; eapply DARewriteIffPL; first by d_head.
      rewrite_assertion_any; d_swap; d_clear.
      by d_ifp; first by d_head; d_false.

    (* Prove for requests *)
    d_ifp.
      d_forallc "e".
      d_ifc; d_splitp; d_splitp; do 2 (d_swap; d_splitp).
      d_rotate 4; do 2 (d_splitp; d_swap); d_subst.
      d_splitc; first by eapply DAPEqual.
      d_splitc; first by eapply DAPEqual.
      d_evalp; d_destructp (fun t => {A: ("n", "m") \in t}).
      d_forallp "Fois"; d_forallp "Fors"; d_forallp {t: "Fs'" $ "n'"}; d_splitp.
      d_destructp (fun t => {A: t = ("Fs'" $ "n'", "Fors", "Fois")}).
      by d_forallp "m"; d_forallp "n"; d_splitp.

    (* Prove for indications *)
    d_ifp.
      d_forallc "i"; d_forallc "e".
      d_ifc; d_splitp; d_splitp; do 2 (d_swap; d_splitp).
      d_rotate 4; do 2 (d_splitp; d_swap); d_subst.
      d_evalp; d_destructp (fun t => {A: ("n", "m") \in t}).
      d_forallp "Fois"; d_forallp "Fors"; d_forallp {t: "Fs'" $ "n'"}; d_splitp.
      d_destructp (fun t => {A: t = ("Fs'" $ "n'", "Fors", "Fois")}).
      d_forallp "m"; d_forallp "n"; d_splitp.

      d_destructpairp "i" "e" 0 {t: CFLDeliver $ "n" $ "m"}.
      rewrite_assertion_any; d_splitp; d_rotate 2; d_substp; d_evalp.

      set t1l := {t: "Fs" $ "n'"};
        set t2l : term := {t: []};
        set t3l := {t: [CSLDeliver $ "n" $ "m"]};
        set t1r := {t: "Fs'" $ "n'"};
        set t2r : term := "Fors";
        set t3r : term := "Fois".
        d_destructpairp {t: (t1l, t2l)} t3l {t: (t1r, t2r)} t3r; d_splitp.
        d_destructpairp t1l t2l t1r t2r; d_splitp.
      rewrite_assertion_any;
        rewrite /t1l /t2l /t3l /t1r /t2r /t3r;
        clear t1l t2l t3r t1r t2r t3r.
      d_rotate 3; d_substp; d_evalp; d_swap; d_clear; d_swap; d_substp.
      by d_notp; d_splitc; first by eapply DAPEqual.

    (* Prove for periodics *)
    d_ifp.
      d_ifc; d_splitp; d_splitp; do 2 (d_swap; d_splitp).
      d_rotate 4; do 2 (d_splitp; d_swap); d_subst.
      d_evalp; d_rotate 2; d_substp.
      d_notp; d_splitc; first by eapply DAPEqual.
      by do 4 d_clear.

    by d_head.
  }

  (* By InvL *)
  d_have {A:
    when-on["n'"] (("n", "m") \in "Fs'" $ "n'") /\ when-self =>>
    (when-on["n'"] ((("n", "m") \in "Fs" $ "n'")) /\ when-self \/
      when-on["n'"] when[]-> CSLSend $ "n" $ "m")
  }.
  {
    do 7 d_clear. (* Clean up the context *)

    (* Instantiate InvL *)
    eapply DSCut; first by apply DPInvL with (A := {A:
        when-on["n'"] (("n", "m") \in "Fs'" $ "n'") ->
        (when-on["n'"] (("n", "m") \in "Fs" $ "n'") \/
          when-on["n'"] when[]-> CSLSend $ "n" $ "m")});
      first by repeat constructor.

    (* Prove for requests *)
    d_ifp.
      d_forallc "e".
      d_ifc; d_splitp; d_splitp; d_swap; d_splitp.
      d_rotate 3; d_substp; d_evalp.
      d_destructp (fun t => {A: ("Fs'" $ "Fn", "Fors", "Fois") = t}).
      d_forallp "m"; d_forallp "n"; d_splitp.

      d_ifc; d_splitp; d_right; do 2 d_substc.
      d_splitc; first by eapply DAPEqual.
      d_splitc; first by eapply DAPEqual.
      d_splitc; first by eapply DAPEqual.
      by eapply DAPEqual.

    (* Prove for indications *)
    d_ifp.
      d_forallc "i"; d_forallc "e".
      d_ifc; d_splitp; d_splitp; d_swap; d_splitp.
      d_rotate 3; d_substp; d_evalp.
      d_destructp (fun t => {A: ("Fs'" $ "Fn", "Fors", "Fois") = t}).
      d_forallp "m"; d_forallp "n"; d_splitp.

      d_ifc; d_splitp; d_left; do 2 d_substc.
      d_splitc; first by eapply DAPEqual.

      d_rotate 3; d_substp; d_evalp.
      d_destructpairp {t: ("Fs'" $ "n'", "Fors")} "Fois"
        {t: ("Fs" $ "n'", [])} {t: [CSLDeliver $ "n" $ "m"]}; d_splitp.
      d_destructpairp {t: "Fs'" $ "n'"} "Fors"
        {t: "Fs" $ "n'"} {t: []}; d_splitp.
      by d_rotate 7; d_substp.

    (* Prove for periodics *)
    d_ifp.
      d_ifc; d_splitp; d_splitp; d_swap; d_splitp.
      d_rotate 3; d_substp; d_evalp.

      d_ifc; d_splitp; d_left; d_substc.
      d_splitc; first by eapply DAPEqual.

      d_rotate 2; d_substp.
      set t := {t: FMap $
        (fun: match: #0 with: {{(#, #) -> CPair $ 0 $ (CFLSend $ #0 $ #1)}}) $
        ("Fs" $ "n'")}.
      d_destructpairp {t: ("Fs'" $ "n'", "Fors")} {t: "Fois"}
        {t: ("Fs" $ "n'", t)} {t: []}; d_splitp;
        d_destructpairp {t: "Fs'" $ "n'"} "Fors" {t: "Fs" $ "n'"} t; d_splitp;
        rewrite {}/t.
      by d_rotate 7; d_substp.

    eapply DARewriteIffPL; first by apply DSMergeIf with
      (Ap1 := {A: when-self})
      (Ap2 := {A: when-on["n'"] (("n", "m") \in "Fs'" $ "n'")})
      (Ac := {A: when-on["n'"] ((("n", "m") \in "Fs" $ "n'")) \/
        when-on["n'"] when[]-> CSLSend $ "n" $ "m"}).
    eapply DARewriteIffPL; first by apply DSAndCommutative with
      (Acl := {A: when-self})
      (Acr := {A: when-on["n'"] (("n", "m") \in "Fs'" $ "n'")}).
    eapply DARewriteIffPL; first by apply DSIfAndIntroduce with
      (Apl := {A: when-on["n'"] (("n", "m") \in "Fs'" $ "n'")})
      (Apr := {A: when-self})
      (Ac := {A: when-on["n'"] (("n", "m") \in "Fs" $ "n'") \/
        when-on["n'"] when[]-> CSLSend $ "n" $ "m"}).
    eapply DARewriteIffPL; first by apply DSOrDistributesAnd with
      (Al := {A: when-on["n'"] (("n", "m") \in "Fs" $ "n'")})
      (Ar := {A: when-on["n'"] when[]-> CSLSend $ "n" $ "m"})
      (A := {A: when-self}).
    eapply DARewriteIffPL; first by apply DSAndAssociative with
      (Al := {A: "Fn" = "n'"})
      (Am := {A: when[]-> CSLSend $ "n" $ "m"})
      (Ar := {A: when-self}).
    eapply DARewriteIffPL.
      eapply DSCut; first by apply DPWhenTopRequestSelfEliminate.
      d_forallp {t: CSLSend $ "n" $ "m"}; d_head.
    by [].
  }

  (* By InvL *)
  d_have {A:
    when-on["n'"] ((0, CFLSend $ "n" $ "m") \in "Fors") /\ when-self =>>
    when-on["n'"] (("n", "m") \in "Fs'" $ "n'") /\ when-self
  }.
  {
    do 7 d_clear. (* Clean up the context *)

    (* Instantiate InvL *)
    eapply DSCut; first by apply DPInvL with (A := {A:
        when-on["n'"] ((0, CFLSend $ "n" $ "m") \in "Fors") ->
        when-on["n'"] (("n", "m") \in "Fs'" $ "n'")
      }); first by repeat constructor.

    (* Prove for requests *)
    d_ifp.
      d_forallc "e".
      d_ifc; d_splitp; d_splitp; d_swap; d_splitp.
      d_rotate 3; d_evalp.
      d_destructp (fun t => {A: ("Fs'" $ "Fn", "Fors", "Fois") = t}).
      d_forallp "m"; d_forallp "n"; d_splitp; d_swap.
      d_substp; d_evalp.
      set t1l := {t: "Fs'" $ "Fn"};
        set t2l := {t: "Fors"};
        set t3l := {t: "Fois"};
        set t1r := {t: ("Fs" $ "Fn") \union [("n", "m")]};
        set t2r := {t: [(0, CFLSend $ "n" $ "m")]};
        set t3r := {t: []};
        d_destructpairp {t: (t1l, t2l)} t3l {t: (t1r, t2r)} t3r;
        d_destructpairp t1l t2l t1r t2r;
        rewrite_assertion_any;
        rewrite /t1l /t2l /t3l /t1r /t2r /t3r /t1r;
        clear t1l t2l t3l t1r t2r t3r;
        do 2 d_splitp.
      d_ifc; d_splitp; d_splitc; first by d_head.
      d_swap; d_clear; d_swap; d_subst.
      eapply DSCut; first by apply DAPInUnion.
      d_forallp {t: "Fs" $ "n'"};
        d_forallp {t: [("n", "m")]};
        d_forallp {t: ("n", "m")}.
      by d_ifp; first by d_right; eapply DAPIn.

    (* Prove for indications *)
    d_ifp.
      (* Obtain the first contradictory premise *)
      d_forallc "i"; d_forallc "e".
      d_ifc; d_splitp; d_swap; d_evalp.
      d_destructp (fun t => {A: ("Fs'" $ "Fn", "Fors", "Fois") = t}).
      d_forallp "m"; d_forallp "n"; d_splitp; d_swap.
      d_substp; d_evalp.
      set t1l := {t: "Fs'" $ "Fn"};
        set t2l := {t: "Fors"};
        set t3l := {t: "Fois"};
        set t1r := {t: ("Fs" $ "Fn")};
        set t2r := {t: []};
        set t3r := {t: [CSLDeliver $ "n" $ "m"]};
        d_destructpairp {t: (t1l, t2l)} t3l {t: (t1r, t2r)} t3r;
        d_destructpairp t1l t2l t1r t2r;
        rewrite_assertion_any;
        rewrite /t1l /t2l /t3l /t1r /t2r /t3r /t1r;
        clear t1l t2l t3l t1r t2r t3r;
        do 2 d_splitp.
      d_clear; do 3 (d_swap; d_clear). (* Clean up the context *)

      (* Obtain the second contradictory premise *)
      d_ifc; d_splitp; d_clear; d_substp.

      (* Prove the contradiction *)
      eapply DSCut; first by eapply DAPInNil.
      d_forallp {t: (0, CFLSend $ "n" $ "m")}.
      eapply DSCut; first by eapply DSNotImpliesFalse with (Ac := {A:
        (0, CFLSend $ "n" $ "m") \in CNil}).
      d_swap; eapply DARewriteIffPL; first by d_head.
      rewrite_assertion_any; d_swap; d_clear.
      by d_ifp; first by d_head; d_false.

    (* Prove for periodics *)
    d_ifp.
      d_ifc; d_splitp; d_swap; d_evalp.
      set tf := {t: fun: match: #0 with: {{(#, #) -> (0, CFLSend $ #0 $ #1)}}}.
      set ts := {t: FMap $ tf $ ("Fs" $ "Fn")};
      d_destructpairp {t: ("Fs'" $ "Fn", "Fors")} "Fois"
        {t: ("Fs" $ "Fn", ts)} {t: []}; d_splitp;
      d_destructpairp {t: "Fs'" $ "Fn"} "Fors"
        {t: "Fs" $ "Fn"} ts; d_splitp;
        rewrite {}/ts.
      d_ifc; d_splitp; d_splitc; first by d_head.
      d_swap; d_substp; d_rotate 2; d_subst; d_rotate 5.
      eapply DSCut; first by apply DAPInMap.
      d_forallp tf; d_forallp {t: ("n", "m")}; d_forallp {t: "Fs" $ "Fn"}.
      d_splitp; d_clear; d_evalp; d_ifp; first by d_head.
      by d_substp.

    eapply DARewriteIffPL; first by apply DSMergeIf with
      (Ap1 := {A: when-self})
      (Ap2 := {A: when-on["n'"] ((0, CFLSend $ "n" $ "m") \in "Fors")})
      (Ac := {A: when-on["n'"] (("n", "m") \in "Fs'" $ "n'")}).
    eapply DARewriteIffPL; first by apply DSAndCommutative with
      (Acl := {A: when-self})
      (Acr := {A: when-on["n'"] ((0, CFLSend $ "n" $ "m") \in "Fors")}).
    by eapply DARewriteIffPL; first by apply DSIfAndIntroduce with
      (Apl := {A: when-on["n'"] ((0, CFLSend $ "n" $ "m") \in "Fors")})
      (Apr := {A: when-self})
      (Ac := {A: when-on["n'"] (("n", "m") \in "Fs'" $ "n'")}).
  }

  (* By (8) and (9) *)
  d_have {A:
    when-on["n'"] ((0, CFLSend $ "n" $ "m") \in "Fors") /\ when-self =>>
    (when-on["n'"] (("n", "m") \in "Fs" $ "n'")) /\ when-self \/
      when-on["n'"] when[]-> CSLSend $ "n" $ "m"
  }.
  {
    eapply DARewriteIffPL; first by eapply DSCut;
      first by apply DSIfAndIntroduce with
        (Apl := {A: when-on["n'"] ((0, CFLSend $ "n" $ "m") \in "Fors")})
        (Apr := {A: when-self})
        (Ac := {A: when-on["n'"] (("n", "m") \in "Fs'" $ "n'")}).
    by eapply DARewriteEntailsP; first by d_head.
  }

  (* By (6) and (10) *)
  d_have {A:
    when-on["n'"] when[0]-> CFLSend $ "n" $ "m" <~
    (when-on["n'"] (("n", "m") \in "Fs" $ "n'")) /\ when-self \/
    when-on["n'"] when[]-> CSLSend $ "n" $ "m"
  }.
  {
    by d_rotate 4; eapply DARewriteEntailsP; first by d_rotate 5; d_head.
  }

  (* By (7) and (11) *)
  d_have {A:
    when-on["n'"] when[0]-> CFLSend $ "n" $ "m" <~
    when-on["n'"] when[]-> CSLSend $ "n" $ "m"
  }.
  {
    eapply DARewriteEntailsP; first by d_rotate 3; d_head.
    eapply DARewriteIffPL; first by apply DSOrCommutative with
      (Acl := {A: eventuallyp^ when-on["n'"] when[]-> CSLSend $ "n" $ "m"})
      (Acr := {A: when-on["n'"] when[]-> CSLSend $ "n" $ "m"}).
    by eapply DARewriteCongruentCL;
      first by apply DTL83_1 with
      (A := {A: when-on["n'"] when[]-> CSLSend $ "n" $ "m"}).
  }

  (* From (5) and (12) *)
  d_have {A:
    when-on["n"] when[]<- CSLDeliver $ "n'" $ "m" <~
    eventuallyp when-on["n'"] when[]-> CSLSend $ "n" $ "m"
  }.
  {
    by d_rotate 7; eapply DARewriteEntailsP;
      first by d_rotate 4; d_head.
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
Qed.
