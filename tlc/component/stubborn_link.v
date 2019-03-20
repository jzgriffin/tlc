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
    (s, (fun: let: (#, #) := #(0, 0) in:
      (flc, CFLSend $ #(0, 0) $ #(0, 1))) <$> s, [])
  }.

(* Specification *)

(* Stubborn delivery
 * If a correct node n sends a message m to a correct node n', then n'
 * delivers m infinitely often *)
Theorem SL_1 : Context [:: V "m"; V "n'"; V "n"] [::] |- stubborn_link, {A:
  correct "n" /\ correct "n'" ->
  on "n", event []-> CSLSend $ "n'" $ "m" =>>
  always eventually on "n'", event []<- CSLDeliver $ "n" $ "m"
}.
Proof.
  (* Introduce context *)
  set C := stubborn_link; rewrite -/C.
  d_ifc; d_splitp.

  (* By IR *)
  d_have {A:
    on "n", event []-> CSLSend $ "n'" $ "m" =>>
    self-event /\ ("n'", "m") \in ("Fs'" $ "n")
  }.
  {
    (* Instantiate IR *)
    d_use DPIR; d_forallp {t: CSLSend $ "n'" $ "m"}; d_evalp.

    d_destructtuplep
      {t: "Fs'" $ "Fn"} {t: "Fors"} {t: "Fois"}
      {t: ("Fs" $ "Fn") \union [("n'", "m")]}
        {t: [(0, CFLSend $ "n'" $ "m")]} {t: []}.

    d_have {A: ("Fs'" $ "Fn" = "Fs" $ "Fn" \union [("n'", "m")] /\
      "Fors" = [(0, CFLSend $ "n'" $ "m")]) /\ "Fois" = [] ->
      ("n'", "m") \in "Fs'" $ "Fn"}.
      d_ifc; d_splitp; d_splitp; d_substc.
      eapply DSCut; first by eapply DAPInUnion.
      d_forallp {t: "Fs" $ "Fn"};
        d_forallp {t: [("n'", "m")]};
        d_forallp {t: ("n'", "m")}.
      by d_ifp; first by by d_right; eapply DAPIn.
    d_swap; eapply DARewriteIfP; first by d_head.
    rewrite_assertion_pos.

    eapply DSCut; first by apply DSIfAndSplit with
      (Ap := {A: event []-> CSLSend $ "n'" $ "m"})
      (Acl := {A: self-event})
      (Acr := {A: ("n'", "m") \in "Fs'" $ "Fn"}).
    d_splitp; d_swap; d_clear; d_ifp.
      d_splitc; last by d_splitp.
      d_use DPTopRequestSelf.
      by d_forallp {t: CSLSend $ "n'" $ "m"}; d_splitp.

    do 4 (d_swap; d_clear). (* Clean up the context *)
    d_have {A: on "n", event []-> CSLSend $ "n'" $ "m" -> self-event /\
      ("n'", "m") \in "Fs'" $ "n"}.
      d_ifc; d_splitp; d_rotate 2.
      d_ifp; first by d_swap.
      by d_subst.

    by d_have {A: on "n", event []-> CSLSend $ "n'" $ "m" =>> self-event /\
      ("n'", "m") \in "Fs'" $ "n"}; first by apply DTGeneralization.
  }

  (* By InvS'' *)
  d_have {A:
    self-event /\ ("n'", "m") \in ("Fs'" $ "n") =>>
    always^ (self-event -> ("n'", "m") \in ("Fs" $ "n"))
  }.
  {
    (* Instantiate InvS'' *)
    set S := fun ts => {A: ("n'", "m") \in ts}.
    eapply DSCut; first by apply DPInvS'' with (S := S).
    d_forallp "n".

    (* Prove property for requests *)
    d_ifp.
      d_forallc "s"; d_forallc "e"; d_ifc.
      eapply DARewriteIffPL; first by
        d_use DAPConcatIn; d_forallp {t: ("n'", "m")}; d_forallp "s".
      rewrite_assertion_any.

      d_existsp "sl"; d_existsp "sr"; d_evalc.
      d_destructc (fun t => {A: ("n'", "m") \in
        match: t with: {{(#, %, %) -> #(0, 0)}}}).
      d_forallc "?n"; d_forallc "?m".
      d_ifc; d_substc; d_evalc.

      d_use DAPInUnion.
      d_forallp {t: "sl" ++ [("n'", "m")] ++ "sr"};
        d_forallp {t: [("?m", "?n")]};
        d_forallp {t: ("n'", "m")}.
      d_ifp.
        d_left.
        d_use DAPInConcat.
        d_forallp {t: "sl"};
          d_forallp {t: [("n'", "m")] ++ "sr"};
          d_forallp {t: ("n'", "m")}.
        d_ifp.
          d_right.
          d_use DAPInConcat.
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
        match: t with: {{(#, %, %) -> #(0, 0)}}}).
      d_forallc "?n"; d_forallc "?m".
      by d_ifc; d_substc; d_evalc; d_clear.

    (* Prove property for periodics *)
    d_ifp.
      by d_forallc "s"; d_ifc; d_evalc.

    by [].
  }

  (* From (2) and (3) *)
  d_have {A:
    on "n", event []-> CSLSend $ "n'" $ "m" =>>
    always^ (self-event -> ("n'", "m") \in ("Fs" $ "n"))
  }.
  {
    by d_rotate 1; eapply DARewriteEntailsP;
      first by d_rotate 2; d_head.
  }

  (* By APerSA *)
  d_have {A:
    correct "n" -> (self-event -> ("n'", "m") \in ("Fs" $ "n")) =>>
    always eventually on "n",
      (self-event /\ (0, CFLSend $ "n'" $ "m") \in "Fors")
  }.
  {
    d_ifc; d_clear.

    (* Instantiate APerSA *)
    set S := fun ts => {A: ("n'", "m") \in ts}.
    set A := {A: on "n",
      (self-event /\ (0, CFLSend $ "n'" $ "m") \in "Fors")}.
    eapply DSCut; first by apply DPAPerSA with (S := S) (A := A);
      first by repeat constructor.
    d_forallp "n".

    d_ifp.
      d_ifc; do 3 (d_splitp; d_swap).
      d_evalp.
      set tf := {t: fun:
          match: #(0, 0) with:
          {{ (#, #) -> (0, CFLSend $ #(0, 0) $ #(0, 1)) }}
        };
        d_destructtuplep
          {t: "Fs'" $ "n"} {t: "Fors"} {t: "Fois"}
          {t: ("Fs" $ "n")} {t: FMap $ tf $ ("Fs" $ "n")} {t: []};
        do 2 d_splitp.

      d_splitc; first by d_assumption.
      d_splitc; first by d_assumption.
      d_substc.
      d_use DAPInMap.
      d_forallp tf; d_forallp {t: ("n'", "m")};
        d_forallp {t: "Fs" $ "n"}.
      d_splitp; d_swap; d_clear; d_ifp; first by d_rotate 3; d_head.
      by d_evalp.

    by d_ifp; first by d_assumption.
  }

  (* From (4) and (5) *)
  d_have {A:
    on "n", event []-> CSLSend $ "n'" $ "m" =>>
    always^ eventually on "n",
      (self-event /\ (0, CFLSend $ "n'" $ "m") \in "Fors")
  }.
  {
    d_ifp; first by d_assumption.
    d_rotate 1; eapply DARewriteEntailsP; first by d_rotate 4; d_head.
    rewrite_assertion_pos.
    by eapply DARewriteCongruentCR; first by apply DTL119 with (A := {A:
      eventually on "n",
        (self-event /\ (0, CFLSend $ "n'" $ "m") \in "Fors")
      }).
  }

  (* From OR *)
  (* NOTE: send_fl(n, m) should be send_fl(n', m) *)
  d_have {A:
    on "n", (self-event /\ (0, CFLSend $ "n'" $ "m") \in "Fors") =>>
    eventually^ on "n", event [0]-> CFLSend $ "n'" $ "m"
  }.
  {
    (* Instantiate OR *)
    by d_use DPOR;
      d_forallp "n"; d_forallp 0; d_forallp {t: CFLSend $ "n'" $ "m"}.
  }

  (* From (6) and (7) *)
  (* NOTE: send_fl(n, m) should be send_fl(n', m) *)
  d_have {A:
    on "n", event []-> CSLSend $ "n'" $ "m" =>>
    always^ eventually eventually^ on "n", event [0]-> CFLSend $ "n'" $ "m"
  }.
  {
    by d_rotate 1; eapply DARewriteEntailsP;
      first by d_rotate 6; d_head.
  }

  (* From lemma 120 on (8) *)
  (* NOTE: Lemma 84 does not apply here; must use new lemma 120 instead *)
  d_have {A:
    on "n", event []-> CSLSend $ "n'" $ "m" =>>
      always^ eventually^ on "n", event [0]-> CFLSend $ "n'" $ "m"
  }.
  {
    by eapply DARewriteEntailsP; first by apply DTL120_3 with (A := {A:
      on "n", event [0]-> CFLSend $ "n'" $ "m"}).
  }

  (* By rule FLoss on (1) and (9) *)
  d_have {A:
    on "n", event []-> CSLSend $ "n'" $ "m" =>>
    always^ eventually^ on "n'", event [0]<- CFLDeliver $ "n" $ "m"
  }.
  {
    (* Instantiate FLoss *)
    d_use DPFLoss.
    d_forallp "n"; d_forallp "n'"; d_forallp "m"; d_forallp 0.
    d_ifp; first by d_assumption.

    by d_rotate 1; eapply DARewriteIfP;
      first by by d_rotate 9; d_head.
  }

  (* From rule IIOI *)
  d_have {A:
    on "n'", event [0]<- CFLDeliver $ "n" $ "m" =>>
    eventually^ on "n'", event []<- CSLDeliver $ "n" $ "m"
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
      {A: on  "n'", event [ 0 ]<- CFLDeliver $ "n" $ "m"}).
  }

  (* From (10) and (11) *)
  d_have {A:
    on "n", event []-> CSLSend $ "n'" $ "m" =>>
    always^ eventually^ eventually^
      on "n'", event []<- CSLDeliver $ "n" $ "m"
  }.
  {
    by d_rotate 1; eapply DARewriteEntailsP;
      first by d_rotate 10; d_head.
  }

  (* From lemma 84 and (12) *)
  (* NOTE: Lemma 84 does not apply here; must use new lemma 120 instead *)
  d_have {A:
    on "n", event []-> CSLSend $ "n'" $ "m" =>>
    always^ eventually^
      on "n'", event []<- CSLDeliver $ "n" $ "m"
  }.
  {
    by eapply DARewriteEntailsP; first by apply DTL120_2 with (A := {A:
      on "n'", event []<- CSLDeliver $ "n" $ "m"}).
  }

  eapply DARewriteIfP; first by apply DTL121 with (A := {A:
    on "n'", event []<- CSLDeliver $ "n" $ "m"}).
  by eapply DARewriteIfP; first by apply DTL122 with (A := {A:
    on "n'", event []<- CSLDeliver $ "n" $ "m"}).
Qed.

(* No-forge
 * If a node n delivers a message m with sender n', then m was previously sent
 * to n by n' *)
Theorem SL_2 : Context [:: V "m"; V "n'"; V "n"] [::] |- stubborn_link, {A:
  on "n", event []<- {t: CSLDeliver $ "n'" $ "m"} <~
  on "n'", event []-> {t: CSLSend $ "n" $ "m"}
}.
Proof.
  pose C := stubborn_link; rewrite -/C.

  (* By OI' *)
  d_have {A:
    on "n", event []<- CSLDeliver $ "n'" $ "m" =>>
    eventuallyp (self-event /\ on "n", (CSLDeliver $ "n'" $ "m" \in "Fois"))
  }.
  {
    (* Instantiate OI' *)
    d_use DPOI'; d_forallp "n"; d_forallp {t: CSLDeliver $ "n'" $ "m"}.

    by eapply DARewriteIfP; first by apply DTL123 with (A := {A:
      self-event /\ on "n", (CSLDeliver $ "n'" $ "m" \in "Fois")}).
  }

  (* By InvL *)
  d_have {A:
    self-event /\ on "n", (CSLDeliver $ "n'" $ "m" \in "Fois") =>>
    on "n", event [0]<- CFLDeliver $ "n'" $ "m"
  }.
  {
    d_clear. (* Clean up the context *)

    (* Instantiate InvL *)
    eapply DSCut; first by apply DPInvL with (A := {A:
        on "n", (CSLDeliver $ "n'" $ "m" \in "Fois") ->
        on "n", event [0]<- CFLDeliver $ "n'" $ "m"
      }); first by repeat constructor.

    (* Prove for requests *)
    d_ifp.
      (* Obtain the first contradictory premise *)
      d_forallc "e".
      d_ifc; d_splitp; d_swap; d_evalp.
      d_destructp (fun t => {A: ("Fs'" $ "Fn", "Fors", "Fois") = t}).
      d_forallp "m"; d_forallp "n'"; d_splitp; d_swap.
      d_substp; d_evalp.
      d_destructtuplep
        {t: "Fs'" $ "Fn"} {t: "Fors"} {t: "Fois"}
        {t: ("Fs" $ "Fn") \union [("n'", "m")]}
          {t: [(0, CFLSend $ "n'" $ "m")]} {t: []};
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
      d_destructtuplep
        {t: "Fs'" $ "Fn"} {t: "Fors"} {t: "Fois"}
        {t: "Fs" $ "Fn"} {t: []} {t: [CSLDeliver $ "n'" $ "m"]};
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
      d_destructtuplep
        {t: "Fs'" $ "Fn"} {t: "Fors"} {t: "Fois"}
        {t: "Fs" $ "Fn"}
          {t: (fun: match: #(0, 0) with:
            {{ (#, #) -> (0, CFLSend $ #(0, 0) $ #(0, 1)) }}) <$>
            ("Fs" $ "Fn")}
          {t: []};
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

    by eapply DARewriteIffPL; first by apply DSMergeIf with
      (Ap1 := {A: self-event})
      (Ap2 := {A: on "n", (CSLDeliver $ "n'" $ "m" \in "Fois")})
      (Ac := {A: on "n", event [0]<- CFLDeliver $ "n'" $ "m"}).
  }

  (* From (1) and (2) *)
  d_have {A:
    on "n", event []<- CSLDeliver $ "n'" $ "m" <~
    on "n", event [0]<- CFLDeliver $ "n'" $ "m"
  }.
  {
    by d_rotate 1; eapply DARewriteEntailsP; first by d_head.
  }

  (* By NForge *)
  d_have {A:
    on "n", event [0]<- CFLDeliver $ "n'" $ "m" <~
    on "n'", event [0]-> CFLSend $ "n" $ "m"
  }.
  {
    (* Instantiate NForge *)
    by d_use DPNForge;
      d_forallp "n'"; d_forallp "n"; d_forallp "m"; d_forallp 0.
  }

  (* By lemma 85 on (3) and (4) *)
  d_have {A:
    on "n", event []<- CSLDeliver $ "n'" $ "m" <~
    on "n'", event [0]-> CFLSend $ "n" $ "m"
  }.
  {
    eapply DTL85.
    - by d_rotate 1.
    - by [].
  }

  (* By OR' *)
  d_have {A:
    on "n'", event [0]-> CFLSend $ "n" $ "m" =>>
    eventuallyp (self-event /\ on "n'",
      ((0, CFLSend $ "n" $ "m") \in "Fors"))
  }.
  {
    (* Instantiate OR' *)
    d_use DPOR';
      d_forallp "n'"; d_forallp 0; d_forallp {t: CFLSend $ "n" $ "m"}.

    by eapply DARewriteIfP; first by apply DTL123 with (A := {A:
      self-event /\ on "n'", ((0, CFLSend $ "n" $ "m") \in "Fors")}).
  }

  (* By InvSA *)
  d_have {A:
    self-event /\ on "n'", (("n", "m") \in "Fs" $ "n'") =>>
    eventuallyp^ on "n'", event []-> CSLSend $ "n" $ "m"
  }.
  {
    do 6 d_clear. (* Clean up the context *)

    (* Instantiate InvSA *)
    eapply DSCut; first by apply DPInvSA with
      (S := fun ts => {A: on "n'", (("n", "m") \in ts)})
      (A := {A: event []-> CSLSend $ "n" $ "m"});
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

      d_destructtuplep
        {t: "Fs" $ "n'"} {t: []} {t: [CSLDeliver $ "n" $ "m"]}
        {t: "Fs'" $ "n'"} {t: "Fors"} {t: "Fois"};
        do 2 d_splitp.
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
    self-event /\ on "n'", (("n", "m") \in "Fs'" $ "n'") =>>
    (self-event /\ on "n'", ((("n", "m") \in "Fs" $ "n'")) \/
      on "n'", event []-> CSLSend $ "n" $ "m")
  }.
  {
    do 7 d_clear. (* Clean up the context *)

    (* Instantiate InvL *)
    eapply DSCut; first by apply DPInvL with (A := {A:
        on "n'", (("n", "m") \in "Fs'" $ "n'") ->
        (on "n'", (("n", "m") \in "Fs" $ "n'") \/
          on "n'", event []-> CSLSend $ "n" $ "m")});
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
      d_destructtuplep
        {t: "Fs'" $ "n'"} {t: "Fors"} {t: "Fois"}
        {t: "Fs" $ "n'"} {t: []} {t: [CSLDeliver $ "n" $ "m"]};
        do 2 d_splitp.
      by d_rotate 7; d_substp.

    (* Prove for periodics *)
    d_ifp.
      d_ifc; d_splitp; d_splitp; d_swap; d_splitp.
      d_rotate 3; d_substp; d_evalp.

      d_ifc; d_splitp; d_left; d_substc.
      d_splitc; first by eapply DAPEqual.

      d_rotate 2; d_substp.
      set t := {t:
        (fun: match: #(0, 0) with:
          {{ (#, #) -> (0, CFLSend $ #(0, 0) $ #(0, 1)) }}) <$>
          ("Fs" $ "n'")}.
      d_destructtuplep
        {t: "Fs'" $ "n'"} {t: "Fors"} {t: "Fois"}
        {t: "Fs" $ "n'"} {t: t} {t: []};
        do 2 d_splitp.
      by d_rotate 7; d_substp.

    eapply DARewriteIffPL; first by apply DSMergeIf with
      (Ap1 := {A: self-event})
      (Ap2 := {A: on "n'", (("n", "m") \in "Fs'" $ "n'")})
      (Ac := {A: on "n'", ((("n", "m") \in "Fs" $ "n'")) \/
        on "n'", event []-> CSLSend $ "n" $ "m"}).
    eapply DARewriteIffPL; first by apply DSIfAndIntroduce with
      (Apl := {A: self-event})
      (Apr := {A: on "n'", (("n", "m") \in "Fs'" $ "n'")})
      (Ac := {A: on "n'", (("n", "m") \in "Fs" $ "n'") \/
        on "n'", event []-> CSLSend $ "n" $ "m"}).
    eapply DARewriteIffPL; first by apply DSOrDistributesAnd with
      (Al := {A: on "n'", (("n", "m") \in "Fs" $ "n'")})
      (Ar := {A: on "n'", event []-> CSLSend $ "n" $ "m"})
      (A := {A: self-event}).
    eapply DARewriteIffPL; first by apply DSAndCommutative with
      (Acl := {A: "Fn" = "n'"})
      (Acr := {A: event []-> CSLSend $ "n" $ "m"}).
    eapply DARewriteIffPR; first by apply DSAndAssociative with
      (Al := {A: self-event})
      (Am := {A: event []-> CSLSend $ "n" $ "m"})
      (Ar := {A: "Fn" = "n'"}).
    eapply DARewriteIffPL; first by apply DSAndCommutative with
      (Acl := {A: self-event})
      (Acr := {A: event []-> CSLSend $ "n" $ "m"}).
    eapply DARewriteIffPL; first by d_use DPTopRequestSelfEliminate;
      d_forallp {t: CSLSend $ "n" $ "m"}; d_head.
    by eapply DARewriteIffPL; first by apply DSAndCommutative with
      (Acl := {A: event []-> CSLSend $ "n" $ "m"})
      (Acr := {A: "Fn" = "n'"}).
  }

  (* By InvL *)
  d_have {A:
    self-event /\ on "n'", ((0, CFLSend $ "n" $ "m") \in "Fors") =>>
    self-event /\ on "n'", (("n", "m") \in "Fs'" $ "n'")
  }.
  {
    do 7 d_clear. (* Clean up the context *)

    (* Instantiate InvL *)
    eapply DSCut; first by apply DPInvL with (A := {A:
        on "n'", ((0, CFLSend $ "n" $ "m") \in "Fors") ->
        on "n'", (("n", "m") \in "Fs'" $ "n'")
      }); first by repeat constructor.

    (* Prove for requests *)
    d_ifp.
      d_forallc "e".
      d_ifc; d_splitp; d_splitp; d_swap; d_splitp.
      d_rotate 3; d_evalp.
      d_destructp (fun t => {A: ("Fs'" $ "Fn", "Fors", "Fois") = t}).
      d_forallp "m"; d_forallp "n"; d_splitp; d_swap.
      d_substp; d_evalp.
      d_destructtuplep {t: "Fs'" $ "Fn"} {t: "Fors"} {t: "Fois"}
        {t: ("Fs" $ "Fn") \union [("n", "m")]}
          {t: [(0, CFLSend $ "n" $ "m")]} {t: []};
        do 2 d_splitp.
      d_ifc; d_splitp; d_splitc; first by d_head.
      d_swap; d_clear; d_swap; d_subst.
      d_use DAPInUnion.
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
      d_destructtuplep {t: "Fs'" $ "Fn"} {t: "Fors"} {t: "Fois"}
        {t: "Fs" $ "Fn"} {t: []} {t: [CSLDeliver $ "n" $ "m"]};
        do 2 d_splitp.
      d_clear; do 3 (d_swap; d_clear). (* Clean up the context *)

      (* Obtain the second contradictory premise *)
      d_ifc; d_splitp; d_clear; d_substp.

      (* Prove the contradiction *)
      d_use DAPInNil; d_forallp {t: (0, CFLSend $ "n" $ "m")}.
      eapply DSCut; first by apply DSNotImpliesFalse with (Ac := {A:
        (0, CFLSend $ "n" $ "m") \in CNil}).
      d_swap; eapply DARewriteIffPL; first by d_head.
      rewrite_assertion_any; d_swap; d_clear.
      by d_ifp; first by d_head; d_false.

    (* Prove for periodics *)
    d_ifp.
      d_ifc; d_splitp; d_swap; d_evalp.
      set tf := {t: fun: match: #(0, 0) with:
        {{ (#, #) -> (0, CFLSend $ #(0, 0) $ #(0, 1)) }}}.
      d_destructtuplep {t: "Fs'" $ "Fn"} {t: "Fors"} {t: "Fois"}
        {t: "Fs" $ "Fn"} {t: tf <$> ("Fs" $ "Fn")} {t: []};
        do 2 d_splitp.
      d_ifc; d_splitp; d_splitc; first by d_head.
      d_swap; d_substp; d_rotate 2; d_subst; d_rotate 5.
      d_use DAPInMap;
        d_forallp tf; d_forallp {t: ("n", "m")}; d_forallp {t: "Fs" $ "Fn"}.
      d_splitp; d_clear; d_evalp; d_ifp; first by d_head.
      by d_substp.

    eapply DARewriteIffPL; first by apply DSMergeIf with
      (Ap1 := {A: self-event})
      (Ap2 := {A: on "n'", ((0, CFLSend $ "n" $ "m") \in "Fors")})
      (Ac := {A: on "n'", (("n", "m") \in "Fs'" $ "n'")}).
    by eapply DARewriteIffPL; first by apply DSIfAndIntroduce with
      (Apl := {A: self-event})
      (Apr := {A: on "n'", ((0, CFLSend $ "n" $ "m") \in "Fors")})
      (Ac := {A: on "n'", (("n", "m") \in "Fs'" $ "n'")}).
  }

  (* By (8) and (9) *)
  d_have {A:
    self-event /\ on "n'", ((0, CFLSend $ "n" $ "m") \in "Fors") =>>
    (self-event /\ on "n'", (("n", "m") \in "Fs" $ "n'")) \/
      on "n'", event []-> CSLSend $ "n" $ "m"
  }.
  {
    by eapply DARewriteEntailsP; first by d_head.
  }

  (* By (6) and (10) *)
  d_have {A:
    on "n'", event [0]-> CFLSend $ "n" $ "m" <~
    self-event /\ on "n'", (("n", "m") \in "Fs" $ "n'") \/
    on "n'", event []-> CSLSend $ "n" $ "m"
  }.
  {
    by d_rotate 4; eapply DARewriteEntailsP; first by d_rotate 5; d_head.
  }

  (* By (7) and (11) *)
  d_have {A:
    on "n'", event [0]-> CFLSend $ "n" $ "m" <~
    on "n'", event []-> CSLSend $ "n" $ "m"
  }.
  {
    eapply DARewriteEntailsP; first by d_rotate 3; d_head.
    eapply DARewriteIffPL; first by apply DSOrCommutative with
      (Acl := {A: eventuallyp^ on "n'", event []-> CSLSend $ "n" $ "m"})
      (Acr := {A: on "n'", event []-> CSLSend $ "n" $ "m"}).
    by eapply DARewriteCongruentCL; first by apply DTL83_1 with
      (A := {A: on "n'", event []-> CSLSend $ "n" $ "m"}).
  }

  (* From (5) and (12) *)
  d_have {A:
    on "n", event []<- CSLDeliver $ "n'" $ "m" <~
    eventuallyp on "n'", event []-> CSLSend $ "n" $ "m"
  }.
  {
    by d_rotate 7; eapply DARewriteEntailsP;
      first by d_rotate 4; d_head.
  }

  (* By lemma 83 on (9) *)
  (* NOTE: This line is missing from the paper proof *)
  d_have {A:
    on "n", event []<- CSLDeliver $ "n'" $ "m" <~
    on "n'", event []-> CSLSend $ "n" $ "m"
  }.
  {
    by eapply DARewriteCongruentCL; first by apply DTL83_1 with
      (A := {A: on "n'", event []-> CSLSend $ "n" $ "m"}).
  }

  by [].
Qed.

(* Top invariants for properties *)
Definition SL_1_TI : top_invariant (derives_assertion SL_1).
Proof.
  apply LIA, LAEntails.
    by apply LAAnd; apply LACorrect.
  apply LAEntails.
    by apply LAEventOn with (d' := [::]).
  by apply LAAlways, LAEventually, LAEventOn with (d' := [::]).
Defined.

Definition SL_2_TI : top_invariant (derives_assertion SL_2).
Proof.
  rewrite /derives_assertion /top_invariant.
  by apply LIA, LAAlways, LAPrecededBy; apply LAEventOn with (d' := [::]).
Defined.
