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
Require Import tlc.component.component.
Require Import tlc.component.stubborn_link.
Require Import tlc.logic.all_logic.
Require Import tlc.operation.orientation.
Require Import tlc.semantics.all_semantics.
Require Import tlc.syntax.all_syntax.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Functional implementation *)
Definition perfect_link :=
  let slc := 0 in
  Component
  (* initialize *)
  {t: fun:
    (* Begin scoped parameters *)
    let n := {t: #(0, 0)} in
    (* End scoped parameters *)
    (0, [])
  }
  (* request *)
  {t: fun: fun: fun:
    (* Begin scoped parameters *)
    let n := {t: #(2, 0)} in
    let s := {t: #(1, 0)} in
    let ir := {t: #(0, 0)} in
    (* End scoped parameters *)
    let: (#, #) := s in: (* c, r *)
    (* Begin scoped parameters *)
    let n := {t: #(3, 0)} in
    let s := {t: #(2, 0)} in
    let ir := {t: #(1, 0)} in
    let c := {t: #(0, 0)} in
    let r := {t: #(0, 1)} in
    (* End scoped parameters *)
    match: ir with:
    {{ CPLSend $ # $ # (* n', m *) ->
      (* Begin scoped parameters *)
      let n := {t: #(4, 0)} in
      let s := {t: #(3, 0)} in
      let ir := {t: #(2, 0)} in
      let c := {t: #(1, 0)} in
      let r := {t: #(1, 1)} in
      let n' := {t: #(0, 0)} in
      let m := {t: #(0, 1)} in
      (* End scoped parameters *)
      let: # := c.+1 in: (* c' *)
      (* Begin scoped parameters *)
      let n := {t: #(5, 0)} in
      let s := {t: #(4, 0)} in
      let ir := {t: #(3, 0)} in
      let c := {t: #(2, 0)} in
      let r := {t: #(2, 1)} in
      let n' := {t: #(1, 0)} in
      let m := {t: #(1, 1)} in
      let c' := {t: #(0, 0)} in
      (* End scoped parameters *)
      let: # := (slc, CSLSend $ n' $ (c', m)) in: (* or *)
      (* Begin scoped parameters *)
      let n := {t: #(6, 0)} in
      let s := {t: #(5, 0)} in
      let ir := {t: #(4, 0)} in
      let c := {t: #(3, 0)} in
      let r := {t: #(3, 1)} in
      let n' := {t: #(2, 0)} in
      let m := {t: #(2, 1)} in
      let c' := {t: #(1, 0)} in
      let or := {t: #(0, 0)} in
      (* End scoped parameters *)
      ((c', r), [or], [])
    }}
  }
  (* indication *)
  {t: fun: fun: fun:
    (* Begin scoped parameters *)
    let n' := {t: #(2, 0)} in
    let s := {t: #(1, 0)} in
    let ii := {t: #(0, 0)} in
    (* End scoped parameters *)
    let: (#, #) := s in: (* c, r *)
    (* Begin scoped parameters *)
    let n' := {t: #(3, 0)} in
    let s := {t: #(2, 0)} in
    let ii := {t: #(1, 0)} in
    let c := {t: #(0, 0)} in
    let r := {t: #(0, 1)} in
    (* End scoped parameters *)
    match: ii with:
    {{ (slc, CSLDeliver $ # $ (#, #)) (* n, c', m *) ->
       (* Begin scoped parameters *)
      let n' := {t: #(4, 0)} in
      let s := {t: #(3, 0)} in
      let ii := {t: #(2, 0)} in
      let c := {t: #(1, 0)} in
      let r := {t: #(1, 1)} in
      let n := {t: #(0, 0)} in
      let c' := {t: #(0, 1)} in
      let m := {t: #(0, 2)} in
      (* End scoped parameters *)

      match: (#(0, 0), #(0, 1)) \in r with:
      {{
         true -> (#(4, 0), [], [])
         |false ->
          (* ((c, r \union [(n, c')]), [], [CPLDeliver $ n $ m]) *)

          let: # := (#(2, 1) \union [(#(1, 0), #(1, 1))]) in: (* r' *)
          (* Begin scoped parameters *)
          let n' := {t: #(5, 0)} in
          let s := {t: #(4, 0)} in
          let ii := {t: #(3, 0)} in
          let c := {t: #(2, 0)} in
          let r := {t: #(2, 1)} in
          let n := {t: #(1, 0)} in
          let c' := {t: #(1, 1)} in
          let m := {t: #(1, 2)} in
          let r' := {t: #(0, 0)} in
          (* End scoped parameters *)
          let: # := CPLDeliver $ #(2, 0) $ #(2, 2) in: (* oi *)
          (* Begin scoped parameters *)
          let n' := {t: #(6, 0)} in
          let s := {t: #(5, 0)} in
          let ii := {t: #(4, 0)} in
          let c := {t: #(3, 0)} in
          let r := {t: #(3, 1)} in
          let n := {t: #(2, 0)} in
          let c' := {t: #(2, 1)} in
          let m := {t: #(2, 2)} in
          let r' := {t: #(1, 0)} in
          let oi := {t: #(0, 0)} in
          (* End scoped parameters *)
          ((#(4, 0), (#(4, 1) \union [(#(3, 0), #(3, 1))])), [], [CPLDeliver $ #(3, 0) $ #(3, 2)] )

       }}
    }}
  }
  (* periodic *)
  {t: fun: fun:
    (* Begin scoped parameters *)
    let n' := {t: #(1, 0)} in
    let s := {t: #(0, 0)} in
    (* End scoped parameters *)
    (s, [], [])
  }.

(* Specification *)

(* Lowered stubborn link properties *)
Definition PL_SL_1 :
  Context [::] [::] |- perfect_link, {A:
    forall: "n0", "n0'", "m0":
    correct "n0" /\ correct "n0'" ->
    on "n0", event [0]-> CSLSend $ "n0'" $ "m0" =>>
    always eventually on "n0'", event [0]<- CSLDeliver $ "n0" $ "m0"
  }.
Proof.
  d_forallc "n"; d_forallc "n'"; d_forallc "m".

  (* Use the lowering specification on SL_1 *)
  eapply DSCut; first by apply: DPLower SL_1 perfect_link 0 SL_1_TA.
  rewrite /lower_assertion /=.

  eapply DARewriteEntailsP; first by apply DTL124 with
    (Ap := {A: "Fd" <<< [0]})
    (Ac := {A: eventually on "n'", event [0]<- CSLDeliver $ "n" $ "m"}).
  rewrite_assertion_pos.

  eapply DARewriteEntailsP; first by apply DTL124 with
    (Ap := {A: "Fd" <<< [0]})
    (Ac := {A:
      on "n", event [0]-> CSLSend $ "n'" $ "m" ->
      "Fd" <<< [0] ~>
           on "n'", event [0]<- CSLDeliver $ "n" $ "m"}).
  rewrite_assertion_pos.

  eapply DARewriteIffPL; first by apply DSMergeIf with
    (Ap1 := {A: "Fd" <<< [0]})
    (Ap2 := {A: on "n", event [0]-> CSLSend $ "n'" $ "m"})
    (Ac := {A:
      "Fd" <<< [0] ~>
      on "n'", event [0]<- CSLDeliver $ "n" $ "m"
    }).
  rewrite_assertion_any.

  d_ifc. d_swap; d_ifp. d_head.
  set A := {A: "Fd" <<< CCons $ 0 $ CNil}.
  set B := {A: on "n", event [0]-> CSLSend $ "n'" $ "m"}.
  set D := {A: on "n'", event [0]<- CSLDeliver $ "n" $ "m"}.
  d_have {A: always (A -> eventually D) =>> ((always A) -> always (eventually D))}.
  {
    eapply DT4.
  }
  d_swap. eapply DARewriteEntailsP; first by d_head. rewrite_assertion_pos.
  d_subst.
  set A1 := {A: "Fd" <<< CCons $ 0 $ CNil}.
  set B1 := {A: "Fn" = "n" /\ "Fd" = CCons $ 0 $ CNil /\ "Fo" = ORequest /\ "Fe" = CSLSend $ "n'" $ "m"}.
  set D1 := {A: ("Fn" = "n'" /\ "Fd" = CCons $ 0 $ CNil /\ "Fo" = OIndication /\ "Fe" = CSLDeliver $ "n" $ "m")}.
  set AB := {A: A1 /\ B1}.
  eapply DARewriteIffPL; first by apply DSMergeIf with
    (Ap1 := {A: AB})
    (Ap2 := {A: always A1})
    (Ac := {A: always eventually D1}).
  rewrite_assertion_any.
  d_have {A: (AB /\ A1) =>> (AB /\ always A1)}.
  {
    eapply DSCut; first by apply DTL132 with (A1 := {A: AB})
                                             (A2 := {A: A1})
                                             (B1 := {A: AB})
                                             (B2 := {A: A1}).
    d_ifp. d_splitc. eapply DTGeneralization; first by repeat constructor.
    d_ifc. d_head. eapply DTGeneralization; first by repeat constructor.
    d_ifc. d_head.

    d_have {A: A1 -> always A1}.
    {
      d_ifc. eapply DTGeneralization; first by repeat constructor.
      d_head.
    }
    d_swap.
    d_have {A: (AB /\ A1) -> (AB /\ always A1)}.
    {
      d_ifc. d_splitc. d_splitp. d_head. eapply DTGeneralization; first by repeat constructor. d_splitp. d_swap. d_head.
    }

    d_swap. eapply DARewriteIfP with (Arp := {A: AB /\ A1})
                                     (Arc := {A: AB /\ always A1}).
    d_head. rewrite_assertion_pos.
    do 2 (d_swap; d_clear).
    d_head.
  }
  eapply DARewriteEntailsP; first by d_head. rewrite_assertion_pos.

  set A2 := {A: "Fd" <<< CCons $ 0 $ CNil}.
  set B2 := {A: "Fn" = "n" /\ "Fd" = CCons $ 0 $ CNil /\ "Fo" = ORequest /\ "Fe" = CSLSend $ "n'" $ "m"}.

  d_have {A: B1 =>> ((A2 /\ B2) /\ A2)}.
  {
    eapply DTGeneralization; first by repeat constructor.
    d_ifc. d_splitc.
    d_splitc. d_splitp. d_swap. d_splitp.
    d_substc. eapply DAPExtension; repeat constructor. d_head.
    d_splitp. d_swap. d_splitp.
    d_substc. eapply DAPExtension; repeat constructor.
  }
  eapply DARewriteEntailsP; first by d_head. rewrite_assertion_pos.
  set A3 := {A: "Fd" <<< CCons $ 0 $ CNil}.
  set B3 := {A: "Fn" = "n" /\ "Fd" = CCons $ 0 $ CNil /\ "Fo" = ORequest /\ "Fe" = CSLSend $ "n'" $ "m"}.
  d_head.
Qed.

Definition PL_SL_2 :
  Context [::] [::] |- perfect_link, {A:
    forall: "n0", "n0'", "m0":
    on "n0", event [0]<- CSLDeliver $ "n0'" $ "m0" <~
    on "n0'", event [0]-> CSLSend $ "n0" $ "m0"
  }.
Proof.
  d_forallc "n"; d_forallc "n'"; d_forallc "m".

  (* Use the lowering specification on SL_2 *)
  eapply DSCut; first by apply: DPLower SL_2 perfect_link 0 SL_2_TA.
  rewrite /lower_assertion /=.

  eapply DARewriteEntailsP; first by apply DTL124 with
    (Ap := {A: "Fd" <<< [0]})
    (Ac := {A: on "n", event [0]<- CSLDeliver $ "n'" $ "m" ->
      eventuallyp on "n'", event [0]-> CSLSend $ "n" $ "m"}).
  eapply DARewriteEntailsP; first by apply DTL125 with
    (Ap := {A: "Fd" <<< [0]})
    (Ac := {A: on "n", event [0]<- CSLDeliver $ "n'" $ "m" ->
      eventuallyp on "n'", event [0]-> CSLSend $ "n" $ "m"}).
  eapply DARewriteIffPL; first by apply DSMergeIf with
    (Ap1 := {A: "Fd" <<< [0]})
    (Ap2 := {A: on "n", event [0]<- CSLDeliver $ "n'" $ "m"})
    (Ac := {A: eventuallyp on "n'", event [0]-> CSLSend $ "n" $ "m"}).

  d_have {A:
    "Fd" <<< [0] /\ on "n", event [0]<- CSLDeliver $ "n'" $ "m" <->
    on "n", event [0]<- CSLDeliver $ "n'" $ "m"
  }.
  {
    d_splitc; d_ifc.
    - by d_splitp; d_swap; d_head.
    - d_splitc.
      + by d_splitp; d_swap; d_splitp; d_substc; eapply DAPExtension.
      + by d_head.
  }

  d_swap; eapply DARewriteIffPL; first by d_head.

  by eapply DARewriteEntailsP; first by apply DTL80 with
    (A := {A: on "n", event [0]<- CSLDeliver $ "n'" $ "m" <~
      on "n'", event [0]-> CSLSend $ "n" $ "m"}).
Qed.

(* Lemmas used in proving PL_1 *)

Lemma L37_1 :
  Context
    [:: V "m'"; V "c"; V "m"; V "n'"; V "n"; V "c'"; V "r"; V "r'"]
    [:: {A: correct "n"}; {A: correct "n'"}] |- perfect_link, {A:
    self-event /\ on "n", ((0, CSLSend $ "n'" $ ("c", "m")) \in "Fors") =>>
    always^ ~(self-event /\
      on "n", ((0, CSLSend $ "n'" $ ("c", "m'")) \in "Fors"))
  }.
Proof.
  pose C := perfect_link; rewrite -/C.
  (* by INVL *)
  d_have {A: self-event /\ on "n", ((0, CSLSend $ "n'" $ ("c", "m")) \in "Fors") =>>
    ((FLeft $ ( "Fs'" $ "n")) = "c")}.
  {
    do 2 d_clear.
    (* Instantiate InvL *)
    eapply DSCut; first by apply DPInvL with (A := {A:
         on "n", ((0, CSLSend $ "n'" $ ("c", "m")) \in "Fors") ->
                 (FLeft $ ( "Fs'" $ "n")) = "c"});
    first by repeat constructor.

    (* request *)
    d_ifp.
    d_forallc "e".
    d_ifc; d_splitp. d_swap; d_evalp.

    d_destructp (fun t => {A: ("Fs'" $ "Fn", "Fors", "Fois") = t});
      d_forallp "r"; d_forallp "c"; d_splitp; d_swap;
        d_substp; d_evalp.

    d_destructp (fun t => {A: ("Fs'" $ "Fn", "Fors", "Fois") = t});
      d_forallp "m"; d_forallp "n'"; d_splitp; d_swap;
            d_substp; d_evalp.

    d_destructtuplep
      {t: "Fs'" $ "Fn"} {t: "Fors"} {t: "Fois"}
      {t: ((FSucc $ "c"), "r")}
      {t: [(0, CSLSend $ "n'" $ (FSucc $ "c", "m"))]}
      {t: []}.
    do 2 d_splitp.
    d_clear.
    do 4 (d_swap; d_clear).

    d_ifc. d_splitp. d_clear. d_substp.

    eapply DSCut; first by eapply DAPNotInCons.
    d_forallp {t: (CPair $ 0 $ (CSLSend $ "n'" $ (CPair $ "c" $ "m")))}.
    d_forallp {t: (CPair $ 0 $ (CSLSend $ "n'" $ (CPair $ (FSucc $ "c") $ "m")))}.
    d_forallp {t: CNil}.

    d_splitp. d_clear.
    d_ifp. d_splitc.
    d_notc.
    d_destructpairp {t: 0} {t: CSLSend $ "n'" $ (CPair $ "c" $ "m")}
                    {t: 0} {t: CSLSend $ "n'" $ (CPair $ (FSucc $ "c") $ "m")}.
    rewrite_assertion_any; d_splitp.
    d_clear.

    eapply DSEqualEvent.
    d_splitp.
    d_clear.
    eapply DSEqualEvent. d_splitp. d_swap; d_clear.
    eapply DSCut; first by eapply DAPNotEqualToSucc.
    d_forallp "c".
    d_ifp; d_head.
    (* meeting above *)

    d_notc.
    eapply DSCut; first by eapply DAPInNil.
    d_forallp {t: CPair $ 0 $ (CSLSend $ "n'" $ (CPair $ "c" $ "m"))}.
    eapply DSCut; first by eapply DSNotImpliesFalse with (Ac := {A:
           CPair $ 0 $ (CSLSend $ "n'" $ (CPair $ "c" $ "m")) \in CNil}).
    d_swap; eapply DARewriteIffPL; first by d_head.
    rewrite_assertion_any; d_swap; d_clear.
    d_ifp; d_head; d_false.

    eapply DSCut; first by eapply DSNotImpliesFalse with (Ac := {A:
           CPair $ 0 $ (CSLSend $ "n'" $ (CPair $ "c" $ "m"))
                 \in CCons $ (CPair $ 0 $ (CSLSend $ "n'" $ (CPair $ (FSucc $ "c") $ "m"))) $ CNil}).
    d_swap; eapply DARewriteIffPL; first by d_head.
    rewrite_assertion_any; d_swap; d_clear.
    d_ifp.
    d_head.
    d_false.

    (* indication *)
    d_ifp.
    d_forallc "i". d_forallc "e".
    d_ifc; d_splitp. d_swap. d_evalp.
    d_destructp (fun t => {A: ("Fs'" $ "Fn", "Fors", "Fois") = t}).
    d_forallp "r"; d_forallp "c". d_splitp; d_swap;
      d_substp. d_evalp.
    d_destructp (fun t => {A: ("Fs'" $ "Fn", "Fors", "Fois") = t}).
    d_forallp "m". d_forallp "c'". d_forallp "n". d_splitp. d_swap.
    d_substp.
    d_evalp.
    d_destructp (fun t => {A: ("Fs'" $ "Fn", "Fors", "Fois") = t}).

    d_orp.
    (* true case *)
    d_splitp. d_swap. d_substp. d_evalp.
    d_ifc. d_swap.
    d_destructtuplep
      {t: "Fs'" $ "Fn"} {t: "Fors"} {t: "Fois"}
      {t: ("c", "r")}
      {t: CNil}
      {t: CNil}.
    do 2 d_splitp. d_swap. do 2 d_rotate. d_swap. d_substp. d_splitp. d_clear.
    eapply DSCut; first by eapply DAPInNil.
    d_forallp {t: CPair $ 0 $ (CSLSend $ "n'" $ (CPair $ "c" $ "m"))}.
    eapply DSCut; first by eapply DSNotImpliesFalse with (Ac := {A:
        (CPair $ 0 $ (CSLSend $ "n'" $ (CPair $ "c" $ "m")) \in CNil)}).
    d_swap. eapply DARewriteIffPL; first by d_head.
    rewrite_assertion_any. d_ifp. d_swap. d_head.
    d_false.

    (* false case *)
    d_splitp. d_swap. d_substp.
    d_evalp.
    d_destructtuplep
      {t: "Fs'" $ "Fn"} {t: "Fors"} {t: "Fois"}
      {t: ("c", (FUnion $ "r" $ (CCons $ (CPair $ "n" $ "c'") $ CNil)))}
      {t: CNil}
      {t: (CCons $ (CPLDeliver $ "n" $ "m") $ CNil)}.
    do 2 d_splitp.
    d_ifc.
    d_swap. d_clear.
    d_substp. d_splitp. d_swap.
    eapply DSCut; first by eapply DAPInNil.
    d_forallp {t: CPair $ 0 $ (CSLSend $ "n'" $ (CPair $ "c" $ "m"))}.
    eapply DSCut; first by eapply DSNotImpliesFalse with (Ac := {A:
        (CPair $ 0 $ (CSLSend $ "n'" $ (CPair $ "c" $ "m")) \in CNil)}).
    d_swap. eapply DARewriteIffPL; first by d_head.
    rewrite_assertion_any. d_ifp. d_swap. d_head.
    d_false.

    (* periodic *)
    d_ifp.
    d_ifc. d_splitp. d_swap. d_evalp.
    d_destructtuplep
      {t: "Fs'" $ "Fn"} {t: "Fors"} {t: "Fois"}
      {t: "Fs" $ "Fn"}
      {t: CNil}
      {t: CNil}.
    do 2 d_splitp. d_swap.
    d_ifc. d_substp. d_splitp; d_swap.
    eapply DSCut; first by eapply DAPInNil.
    d_forallp {t: CPair $ 0 $ (CSLSend $ "n'" $ (CPair $ "c" $ "m"))}.
    eapply DSCut; first by eapply DSNotImpliesFalse with (Ac := {A:
        (CPair $ 0 $ (CSLSend $ "n'" $ (CPair $ "c" $ "m")) \in CNil)}).
    d_swap. eapply DARewriteIffPL; first by d_head.
    rewrite_assertion_any. d_ifp. d_swap. d_head.
    d_false.

    eapply DTGeneralization; first by repeat constructor.
    d_ifc.
    d_swap. d_splitp. d_ifp.
    d_swap. d_splitp. d_head.
    d_ifp.
    d_swap; d_splitp. d_swap; d_head.
    d_head.
  }

  (* by INVS *)
  d_have {A: self-event /\ ((FLeft $ ("Fs" $ "n")) = "c") =>>
    (self-event =>> (FLeft $ ("Fs" $ "n") = "c"))}.
  {
    do 2 (d_swap; d_clear).

    d_have {A: (self-event -> FLeft $ ("Fs" $ "n") = "c") ->
      self-event =>> FLeft $ ("Fs" $ "n") = "c"}.
    d_ifc.
    eapply DTGeneralization; first by repeat constructor. d_head.
    eapply DARewriteIfC with (Arp := {A: self-event -> FLeft $ ("Fs" $ "n") = "c"})
                             (Arc := {A: self-event =>> FLeft $ ("Fs" $ "n") = "c"}).
    d_head.
    rewrite_assertion_pos.


    eapply DTGeneralization; first by repeat constructor.
    d_ifc.

    d_ifc.
    d_swap. d_splitp; d_swap.
    d_head.
  }

  (* by ASA on [1] and [2] *)
  d_have {A: on "n", self-event /\ ((0, CSLSend $ "n'" $ ("c", "m")) \in "Fors") =>>
    always^ (self-event -> FLeft $ ("Fs" $ "n") = "c")}.
  {
    set S := fun ts => {A: FLeft $ ts = "c"}.
    eapply DSCut; first by eapply DPASA with (S := S)
                               (A := {A: on "n", (CPair $ 0 $ (CSLSend $ "n'" $ (CPair $ "c" $ "m")) \in "Fors")})
                               (A' := {A:  FLeft $ ("Fs" $ "n") = "c"});
    first by repeat constructor.
    d_forallp "n".
    d_ifp.
    d_swap. d_head.
    d_ifp. d_head.

    d_have {A: ("Fn" = "n" /\ self-event) /\ CPair $ 0 $ (CSLSend $ "n'" $ (CPair $ "c" $ "m")) \in "Fors" =>>
      self-event /\ "Fn" = "n" /\ CPair $ 0 $ (CSLSend $ "n'" $ (CPair $ "c" $ "m")) \in "Fors"}.
    {
      eapply DTGeneralization; first by repeat constructor.
      d_ifc. d_splitc. d_splitp. d_splitp. d_swap. d_head.
      d_splitp. d_splitp.
      d_splitc. d_head.
      d_rotate 2. d_head.
    }
    eapply DARewriteEntailsP with (Arp := {A: self-event /\ "Fn" = "n" /\ CPair $ 0 $ (CSLSend $ "n'" $ (CPair $ "c" $ "m")) \in "Fors"})
                                  (Arc := {A: always^ (self-event -> FLeft $ ("Fs" $ "n") = "c")}).
    d_head.
    rewrite_assertion_pos.
    d_subst.
    d_head.
  }

  (* by INVL *)
  d_have {A: self-event /\ (FLeft $ ( "Fs" $ "n")) = "c" =>>
    ~(on "n", (CPair $ 0 $ (CSLSend $ "n'" $ (CPair $ "c" $ "m'")) \in "Fors"))}.
  {
    (* Instantiate InvL *)
    eapply DSCut; first by apply DPInvL with (A := {A:
         (FLeft $ ( "Fs" $ "n")) = "c" ->
         ~(on "n", (CPair $ 0 $ (CSLSend $ "n'" $ (CPair $ "c" $ "m'")) \in "Fors"))});
    first by repeat constructor.

    (* request *)
    d_ifp.
    d_forallc "e".
    d_ifc; d_splitp. d_swap; d_evalp.

    d_destructp (fun t => {A: ("Fs'" $ "Fn", "Fors", "Fois") = t});
      d_forallp "r"; d_forallp "c"; d_splitp; d_swap;
        d_substp; d_evalp.

    d_destructp (fun t => {A: ("Fs'" $ "Fn", "Fors", "Fois") = t});
      d_forallp "m'"; d_forallp "n'"; d_splitp; d_swap;
        d_substp; d_evalp.

    d_destructtuplep
      {t: "Fs'" $ "Fn"} {t: "Fors"} {t: "Fois"}
      {t: ((FSucc $ "c"), "r")}
      {t: [(0, CSLSend $ "n'" $ (FSucc $ "c", "m'"))]}
      {t: []}.
    do 2 d_splitp.
    d_ifc.
    eapply DARewriteIffCL with (Arp := {A: ~("Fn" = "n" /\ CPair $ 0 $ (CSLSend $ "n'" $ (CPair $ "c" $ "m'")) \in "Fors")})
                               (Arc := {A: ("Fn" = "n" /\ CPair $ 0 $ (CSLSend $ "n'" $ (CPair $ "c" $ "m'")) \in "Fors") -> AFalse}).
    eapply DSNotImpliesFalse.
    rewrite_assertion_any.
    d_ifc. d_splitp. d_swap. d_substp.

    eapply DSCut; first by eapply DAPNotInCons.
    d_forallp {t: (CPair $ 0 $ (CSLSend $ "n'" $ (CPair $ "c" $ "m'")))}.
    d_forallp {t: (CPair $ 0 $ (CSLSend $ "n'" $ (CPair $ (FSucc $ "c") $ "m'")))}.
    d_forallp {t: CNil}.
    d_splitp. d_clear.
    d_ifp. d_splitc.
    d_notc.
    d_destructpairp {t: 0} {t: CSLSend $ "n'" $ (CPair $ "c" $ "m'")}
                    {t: 0} {t: CSLSend $ "n'" $ (CPair $ (FSucc $ "c") $ "m'")}.
    rewrite_assertion_any.
    d_splitp.  d_clear.
    eapply DSEqualEvent.
    d_splitp.
    d_clear.
    eapply DSEqualEvent. d_splitp. d_swap; d_clear.
    eapply DSCut; first by eapply DAPNotEqualToSucc.
    d_forallp "c".
    d_ifp; d_head.

    d_notc.
    eapply DSCut; first by eapply DAPInNil.
    d_forallp {t: CPair $ 0 $ (CSLSend $ "n'" $ (CPair $ "c" $ "m'"))}.
    eapply DSCut; first by eapply DSNotImpliesFalse with (Ac := {A:
           CPair $ 0 $ (CSLSend $ "n'" $ (CPair $ "c" $ "m'")) \in CNil}).
    d_swap; eapply DARewriteIffPL; first by d_head.
    rewrite_assertion_any; d_swap; d_clear.
    d_ifp; d_head; d_false.

    eapply DSCut; first by eapply DSNotImpliesFalse with (Ac := {A:
           CPair $ 0 $ (CSLSend $ "n'" $ (CPair $ "c" $ "m'"))
                 \in CCons $ (CPair $ 0 $ (CSLSend $ "n'" $ (CPair $ (FSucc $ "c") $ "m'"))) $ CNil}).
    d_swap; eapply DARewriteIffPL; first by d_head.
    rewrite_assertion_any; d_swap; d_clear.
    d_ifp.
    d_head.
    d_false.

    (* indication *)
    d_ifp.
    d_forallc "i". d_forallc "e".
    d_ifc; d_splitp. d_swap. d_evalp.
    d_destructp (fun t => {A: ("Fs'" $ "Fn", "Fors", "Fois") = t}).
    d_forallp "r"; d_forallp "c". d_splitp; d_swap;
      d_substp. d_evalp.
    d_destructp (fun t => {A: ("Fs'" $ "Fn", "Fors", "Fois") = t}).
    d_forallp "m'". d_forallp "c'". d_forallp "n". d_splitp. d_swap.
    d_substp.
    d_evalp.
    d_destructp (fun t => {A: ("Fs'" $ "Fn", "Fors", "Fois") = t}).

    d_orp.
    (* true case *)
    d_splitp. d_swap. d_substp. d_evalp.
    d_ifc. d_swap.
    d_destructtuplep
      {t: "Fs'" $ "Fn"} {t: "Fors"} {t: "Fois"}
      {t: ("c", "r")}
      {t: CNil}
      {t: CNil}.
    do 2 d_splitp. d_swap.
    eapply DARewriteIffCL with (Arp := {A: ~("Fn" = "n" /\ CPair $ 0 $ (CSLSend $ "n'" $ (CPair $ "c" $ "m'")) \in "Fors")})
                               (Arc := {A: ("Fn" = "n" /\ CPair $ 0 $ (CSLSend $ "n'" $ (CPair $ "c" $ "m'")) \in "Fors") -> AFalse}).
    eapply DSNotImpliesFalse.
    rewrite_assertion_any.
    d_ifc. d_splitp. d_swap. d_substp.

    eapply DSCut; first by eapply DAPInNil.
    d_forallp {t: CPair $ 0 $ (CSLSend $ "n'" $ (CPair $ "c" $ "m'"))}.
    eapply DSCut; first by eapply DSNotImpliesFalse with (Ac := {A:
        (CPair $ 0 $ (CSLSend $ "n'" $ (CPair $ "c" $ "m'")) \in CNil)}).
    d_swap. eapply DARewriteIffPL; first by d_head.
    rewrite_assertion_any. d_ifp. d_swap. d_head.
    d_false.

    (* false case *)
    d_splitp. d_swap. d_substp.
    d_evalp.
    d_destructtuplep
      {t: "Fs'" $ "Fn"} {t: "Fors"} {t: "Fois"}
      {t: ("c", (FUnion $ "r" $ (CCons $ (CPair $ "n" $ "c'") $ CNil)))}
      {t: CNil}
      {t: (CCons $ (CPLDeliver $ "n" $ "m'") $ CNil)}.
    do 2 d_splitp.
    d_ifc. d_rotate 2.
    eapply DARewriteIffCL with (Arp := {A: ~("Fn" = "n" /\ CPair $ 0 $ (CSLSend $ "n'" $ (CPair $ "c" $ "m'")) \in "Fors")})
                               (Arc := {A: ("Fn" = "n" /\ CPair $ 0 $ (CSLSend $ "n'" $ (CPair $ "c" $ "m'")) \in "Fors") -> AFalse}).
    eapply DSNotImpliesFalse.
    rewrite_assertion_any.
    d_ifc. d_splitp. d_swap. d_substp.
    eapply DSCut; first by eapply DAPInNil.
    d_forallp {t: CPair $ 0 $ (CSLSend $ "n'" $ (CPair $ "c" $ "m'"))}.
    eapply DSCut; first by eapply DSNotImpliesFalse with (Ac := {A:
        (CPair $ 0 $ (CSLSend $ "n'" $ (CPair $ "c" $ "m'")) \in CNil)}).
    d_swap. eapply DARewriteIffPL; first by d_head.
    rewrite_assertion_any. d_ifp. d_swap. d_head.
    d_false.

    (* periodic *)
    d_ifp.
    d_ifc. d_splitp. d_swap. d_evalp.
    d_destructtuplep
      {t: "Fs'" $ "Fn"} {t: "Fors"} {t: "Fois"}
      {t: "Fs" $ "Fn"}
      {t: CNil}
      {t: CNil}.
    do 2 d_splitp. d_swap.
    d_ifc.

    eapply DARewriteIffCL with (Arp := {A: ~("Fn" = "n" /\ CPair $ 0 $ (CSLSend $ "n'" $ (CPair $ "c" $ "m'")) \in "Fors")})
                               (Arc := {A: ("Fn" = "n" /\ CPair $ 0 $ (CSLSend $ "n'" $ (CPair $ "c" $ "m'")) \in "Fors") -> AFalse}).
    eapply DSNotImpliesFalse.
    rewrite_assertion_any.
    d_ifc. d_splitp. d_swap. d_substp.
    eapply DSCut; first by eapply DAPInNil.
    d_forallp {t: CPair $ 0 $ (CSLSend $ "n'" $ (CPair $ "c" $ "m'"))}.
    eapply DSCut; first by eapply DSNotImpliesFalse with (Ac := {A:
        (CPair $ 0 $ (CSLSend $ "n'" $ (CPair $ "c" $ "m'")) \in CNil)}).
    d_swap. eapply DARewriteIffPL; first by d_head.
    rewrite_assertion_any. d_ifp. d_swap. d_head.
    d_false.

    d_splitp. d_swap; d_clear.
    eapply DTGeneralization; first by repeat constructor.
    d_ifc. d_splitp. d_rotate 2. d_ifp. d_rotate 5. d_head.
    d_ifp. d_rotate 6. d_head. d_head.
  }

  d_have {A: (self-event -> FLeft $ ("Fs" $ "n") = "c") ->
             (self-event -> (self-event /\ FLeft $ ("Fs" $ "n") = "c"))}.
  {
    d_ifc. d_ifc. d_splitc. d_head. d_swap. d_ifp. d_head. d_head.
  }

  d_rotate 2.
  eapply DARewriteIfP with (Arp := {A: (self-event -> FLeft $ ("Fs" $ "n") = "c")})
                           (Arc := {A: self-event -> self-event /\ FLeft $ ("Fs" $ "n") = "c"}).
  d_rotate 4. d_head.
  rewrite_assertion_pos.

  (* from (3) and (4) *)
  eapply DARewriteEntailsP with (Arp := {A: self-event /\ FLeft $ ("Fs" $ "n") = "c" })
                                (Arc := {A: ~ on "n", (CPair $ 0 $ (CSLSend $ "n'" $ (CPair $ "c" $ "m'")) \in "Fors")}).
  d_rotate 5. d_head.
  rewrite_assertion_pos.

  d_have {A:
            (self-event -> ~ on "n", (CPair $ 0 $ (CSLSend $ "n'" $ (CPair $ "c" $ "m'")) \in "Fors")) ->
            ~ (self-event /\ on "n", (CPair $ 0 $ (CSLSend $ "n'" $ (CPair $ "c" $ "m'")) \in "Fors"))}.
  {
    d_ifc.
    eapply DARewriteIffCL with (Arp := {A: ~(self-event /\ "Fn" = "n" /\ CPair $ 0 $ (CSLSend $ "n'" $ (CPair $ "c" $ "m'")) \in "Fors")})
                               (Arc := {A: (self-event /\ "Fn" = "n" /\ CPair $ 0 $ (CSLSend $ "n'" $ (CPair $ "c" $ "m'")) \in "Fors") -> AFalse}).
    eapply DSNotImpliesFalse.
    rewrite_assertion_any.
    d_ifc.
    d_splitp. d_rotate 2. d_ifp. d_rotate 7. d_head.
    d_rotate 9. d_swap.
    eapply DSCut; first by eapply DSNotImpliesFalse with (Ac := {A:
                                                                   on "n", (CPair $ 0 $ (CSLSend $ "n'" $ (CPair $ "c" $ "m'")) \in "Fors")}).
    d_splitp. d_swap; d_clear.
    d_ifp. d_head. d_ifp. d_swap. d_head.
    d_false.
  }
  d_swap.
  eapply DARewriteIfP with (Arp := {A: (self-event -> ~ on "n", (CPair $ 0 $ (CSLSend $ "n'" $ (CPair $ "c" $ "m'")) \in "Fors"))})
                           (Arc := {A:  ~ (self-event /\ on "n", (CPair $ 0 $ (CSLSend $ "n'" $ (CPair $ "c" $ "m'")) \in "Fors"))}).
  d_head.
  rewrite_assertion_pos.

  d_have {A:
            self-event /\ "Fn" = "n" /\ CPair $ 0 $ (CSLSend $ "n'" $ (CPair $ "c" $ "m")) \in "Fors" =>>
                                                                                               ("Fn" = "n" /\ self-event) /\ CPair $ 0 $ (CSLSend $ "n'" $ (CPair $ "c" $ "m")) \in "Fors"
         }.
  {
    eapply DTGeneralization; first by repeat constructor.
    d_ifc. d_splitp. d_swap. d_splitp. d_splitc. d_splitc. d_head.
    d_rotate 2. d_head.
    d_swap. d_head.
  }
  eapply DARewriteEntailsP with (Arc := {A: always^ (~ (self-event /\ on "n", (CPair $ 0 $ (CSLSend $ "n'" $ (CPair $ "c" $ "m'")) \in "Fors")))})
                           (Arp := {A:  ("Fn" = "n" /\ self-event) /\ (CPair $ 0 $ (CSLSend $ "n'" $ (CPair $ "c" $ "m"))) \in "Fors"}).
  d_head.
  rewrite_assertion_pos.

  d_head.
Qed.

Lemma L37_2 :
  Context
    [:: V "m'"; V "c"; V "m"; V "n'"; V "n"; V "c'"; V "r"; V "r'"]
    [:: {A: correct "n"}; {A: correct "n'"}] |- perfect_link, {A:
    self-event /\ on "n", ((0, CSLSend $ "n'" $ ("c", "m")) \in "Fors") =>>
    alwaysp^ ~(self-event /\
      on "n", ((0, CSLSend $ "n'" $ ("c", "m'")) \in "Fors"))
  }.
Proof.

  d_use L37_1.
  eapply DSCut; first by eapply DTL105_1_generalization with (A := {A: self-event /\ on "n", ((0, CSLSend $ "n'" $ ("c", "m")) \in "Fors")})
                                     (A' := {A: (self-event /\
                                                 on "n", ((0, CSLSend $ "n'" $ ("c", "m'")) \in "Fors"))})
                                     (x := {A: "m"})
                                     (x' := {A: "m'"}).
  d_ifp.  d_forallc "m". d_splitc. d_ifc. d_forallc "m". d_head.
  d_ifc. d_forallp "m".  d_head.
  d_ifp.
  d_forallc "m". d_forallc "m'".
  d_head.

  d_forallp "m". d_forallp "m'".
  d_head.
Qed.

Lemma L39 :
  Context
    [:: V "c"; V "m"; V "n'"; V "n"; V "c'"; V "r"; V "r'"]
    [:: {A: correct "n"}; {A: correct "n'"}] |- perfect_link, {A:
    on "n'", event [0]<- CSLDeliver $ "n" $ ("c", "m") /\
    ("n", "c") \notin (FRight $ ("Fs" $ "n'")) =>>
    eventually on "n'", event []<- CPLDeliver $ "n" $ "m"
  }.
Proof.
  pose C := perfect_link; rewrite -/C.

  (* By rule II *)
  d_have {A:
            on "n'", event [0]<- CSLDeliver $ "n" $ ("c", "m") /\
                     ("n", "c") \notin (FRight $ ("Fs" $ "n'")) =>>
                              (*  self-event /\ *)
                          (* ("n", "c") \in (FRight $ ("Fs'" $ "n'")) /\ *)
                        (self-event /\ (CPLDeliver $ "n" $ "m") \in "Fois")}.
  {

      eapply DTGeneralization; first by repeat constructor.
      d_ifc. d_splitp. d_evalp.

      d_use DPII. d_evalp. d_forallp 0.
      d_forallp {t: CSLDeliver $ "n" $ ("c", "m")}. (* d_evalp.*)

      eapply DSEntailsModusPonensP.
      d_eval. d_splitp. d_swap. d_splitp. d_swap. d_splitp.
      d_splitc. do 2 d_rotate. d_head.
      d_splitc. d_head.
      d_swap. d_head.

      d_destructp (fun t => {A: ("Fs'" $ "Fn", "Fors", "Fois") = t
                  }).
      d_forallp {t: "r"}. d_forallp {t: "c'"}.

      d_splitp.
      d_swap. d_substp. d_evalp.
      d_rotate 3. d_substp.
      do 2 (d_swap; d_clear).
      d_rotate 3. do 3 (d_splitp; d_swap). do 3 d_rotate. d_swap.
      eapply DSCut; first by eapply DAPEqualSymmetric.
      d_forallp {t: "Fn"}. d_forallp {t: "n'"}.
      d_splitp. d_ifp. do 2 d_rotate. d_head.
      d_swap. do 1 d_rotate. d_swap. d_substp. do 2 (d_swap; d_clear).
      d_substp. d_evalp.

      d_evalp.

      d_substp.
      d_swap.
      d_destructp (fun t => {A: ("Fs'" $ "Fn", "Fors", "Fois") = t
                  }).

      d_orp.

      (* the true case *)
      d_splitp.
      d_swap; d_substp. d_evalp.
      d_destructtuplep
        {t: "Fs'" $ "Fn"} {t: "Fors"} {t: "Fois"}
        {t: ("c'", "r")}
        {t: CNil}
        {t: CNil}.
      do 2 d_splitp.
      do 3 d_rotate.

      d_swap.
      eapply DSCut; first by apply DSNotImpliesFalse with (Ac := {A: CPair $ "n" $ "c" \in "r"}).
      d_splitp; d_swap; d_clear.
      d_ifp; first by d_head.
      d_swap; d_clear.

      d_swap.
      eapply DSCut; first by apply DAPInEliminateTrue.
      d_forallp {t: ("n", "c")}.
      d_forallp "r".
      d_evalp. d_splitp. d_swap; d_clear.
      d_ifp; first by d_head.
      d_swap; d_clear.
      d_swap;
        d_ifp; first by d_head.
      d_false.
      (* meeting above *)

      (* the false case *)
      d_splitp.
      d_swap.
      d_substp.
      d_evalp.
      d_destructtuplep
        {t: "Fs'" $ "Fn"} {t: "Fors"} {t: "Fois"}
        {t: ("c'", FUnion $ "r" $ (CCons $ (CPair $ "n" $ "c") $ CNil))}
        {t: CNil}
        {t: CCons $ (CPLDeliver $ "n" $ "m") $ CNil}.
      do 2 d_splitp.

      d_splitc.
      d_use DPSecondIndicationSelf.
      d_forallp {t: CSLDeliver $ "n" $ (CPair $ "c" $ "m")}.
      d_splitp. d_swap; d_clear. d_ifp.
      d_splitc. d_rotate 8; first by d_head.
      d_splitc. d_rotate 7; first by d_head.
      d_rotate 6; first by d_head.
      d_head.

      d_subst.
      eapply DAPIn; by []; by [].
    }

    (* by rule OI *)
    d_have {A:
              on "n'", (self-event /\ (CPLDeliver $ "n" $ "m") \in "Fois") =>>
                                                 (eventually^  on "n'", (event []<- CPLDeliver $ "n" $ "m"))
           }.
    {
      d_use DPOI.
        d_forallp "n'";
        d_forallp {t: CPLDeliver $ "n" $ "m"}.

      eapply DARewriteIfP; first by
      apply DTL121 with (A := {A:
                                on "n'", ((CPLDeliver $ "n" $ "m") \in "Fois")}).
      rewrite_assertion_pos.
      d_subst.
      d_head.
    }

    (* clean up and derive the final goal *)
    d_rotate 2. do 2 d_clear.
    d_swap.
    d_have {A:
              (on "n'", event [0]<- CSLDeliver $ "n" $ (CPair $ "c" $ "m") /\ CPair $ "n" $ "c" \notin FRight $ ("Fs" $ "n'") =>>
                                                                                    self-event /\ CPLDeliver $ "n" $ "m" \in "Fois")
              ->
              (on "n'", event [0]<- CSLDeliver $ "n" $ (CPair $ "c" $ "m") /\ CPair $ "n" $ "c" \notin FRight $ ("Fs" $ "n'") =>>
                                                                                    on "n'", (self-event /\ CPLDeliver $ "n" $ "m" \in "Fois"))}.
    d_ifc.
    eapply DTGeneralization; first by repeat constructor. d_ifc.
    d_splitp. d_splitp.
    d_splitc. d_head.
    d_rotate 3.
    eapply DARewriteIfP with (Arp := {A: (on "n'", event [0]<- CSLDeliver $ "n" $ (CPair $ "c" $ "m") /\ CPair $ "n" $ "c" \notin FRight $ ("Fs" $ "n'") =>>
                                                                                                               self-event /\ CPLDeliver $ "n" $ "m" \in "Fois")})
                             (Arc := {A: (on "n'", event [0]<- CSLDeliver $ "n" $ (CPair $ "c" $ "m") /\ CPair $ "n" $ "c" \notin FRight $ ("Fs" $ "n'") ->
                                                   self-event /\ CPLDeliver $ "n" $ "m" \in "Fois")}).
    eapply DT1.
    rewrite_assertion_pos.
    d_ifp. d_rotate 2. d_splitc. d_splitc. d_head. d_swap; first by d_head.
    d_rotate 2. d_head.
    d_head.
    d_swap.

    eapply DARewriteIfP with (Arp := {A: (on "n'", event [0]<- CSLDeliver $ "n" $ (CPair $ "c" $ "m") /\ CPair $ "n" $ "c" \notin FRight $ ("Fs" $ "n'") =>>
                        self-event /\ CPLDeliver $ "n" $ "m" \in "Fois")})
                             (Arc := {A: on "n'", event [0]<- CSLDeliver $ "n" $ (CPair $ "c" $ "m") /\ CPair $ "n" $ "c" \notin FRight $ ("Fs" $ "n'") =>>
                        on "n'", (self-event /\ CPLDeliver $ "n" $ "m" \in "Fois")}).
    d_head.
    rewrite_assertion_pos.
    d_swap; d_clear.
    d_swap.
    eapply DARewriteIfP with (Arp := {A: eventually^ on "n'", event []<- CPLDeliver $ "n" $ "m"})
                             (Arc := {A: eventually on "n'", event []<- CPLDeliver $ "n" $ "m"}).
    eapply DTL121.
    rewrite_assertion_pos.
    d_swap.
    eapply DARewriteEntailsP with (Arp := {A: on "n'", (self-event /\ CPLDeliver $ "n" $ "m" \in "Fois")})
                                  (Arc := {A: eventually on "n'", event []<- CPLDeliver $ "n" $ "m"}).
    d_head.
    rewrite_assertion_pos.
    d_head.
Qed.

Lemma L41 :
  Context
    [:: V "c"; V "m"; V "n'"; V "n"; V "c'"; V "r"; V "r'"]
    [:: {A: correct "n"}; {A: correct "n'"}] |- perfect_link, {A:
    self-event /\ ("n", "c") \in (FRight $ ("Fs" $ "n'")) =>>
    exists: "m": eventuallyp (
      on "n'", event [0]<- CSLDeliver $ "n" $ ("c", "m") /\
      (CPLDeliver $ "n" $ "m") \in "Fois"
    )
  }.
Proof.
  (* Instantiate InvSA *)
  eapply DSCut; first by apply DPInvSA with
                    (S := fun ts => {A: ("n", "c") \in FRight $ ts})
                    (A := {A: exists: "m": (on "n'", event [0]<- CSLDeliver $ "n" $ ("c", "m") /\ (CPLDeliver $ "n" $ "m") \in "Fois")});
  first by repeat constructor.
  d_forallp "n'".
  (* prove for initilization *)
  d_ifp. d_eval.
  eapply DSCut; first by eapply DAPInNil.
  d_forallp {t: CPair $ "n" $ "c"}. d_head.
  (* prove for request *)
  d_ifp. d_forallc "e". d_ifc. d_splitp. do 2 (d_splitp; d_swap). d_splitp.
  d_rotate 4.
  d_subst.
  d_splitp. d_swap. d_eval.
  d_destructp (fun t => {A: ("n", "c") \in match: match: t with: {{(#, %, %) -> P 0 0}} with: {{(%, #) -> P 0 0}} }).
  d_forallp "r". d_forallp "c". d_splitp. d_swap. d_subst. d_eval.

  d_destructp (fun t => {A: ("n", "c") \in match: match: t with: {{(#, %, %) -> P 0 0}} with: {{(%, #) -> P 0 0}} }).
  d_forallp "c". d_forallp "n'".
  d_splitp. d_swap. d_subst. d_eval.
  d_rotate 3. d_subst. d_eval.
  eapply DSCut; first by eapply DSNotImpliesFalse with (Ac := {A:
                                                                 CPair $ "n" $ "c" \in "r"}). d_swap. eapply DARewriteIffPL; first by d_head.
  rewrite_assertion_any. d_swap. d_clear. d_rotate 7.
  eapply DARewriteIfP with (Arp := {A: (CPair $ "n" $ "c" \in "r")})
                           (Arc := {A: AFalse}).
  d_rotate 2. d_head.
  rewrite_assertion_pos. d_false.
  (* prove for indication *)
  d_ifp. d_forallc "i"; d_forallc "e".
  d_ifc. d_splitp; d_splitp; do 2 (d_swap; d_splitp).
  d_rotate 4. d_splitp. d_swap. d_subst. d_eval. d_splitp; d_swap.
  d_destructp (fun t => {A: ("n", "c") \in match: match: t with: {{(#, %, %) -> P 0 0}} with: {{(%, #) -> P 0 0}} }).
  d_forallp "r". d_forallp "c". d_splitp. d_swap. d_subst. d_eval.
  d_destructp (fun t => {A: ("n", "c") \in match: match: t with: {{(#, %, %) -> P 0 0}} with: {{(%, #) -> P 0 0}} }).
  d_forallp "m". d_forallp "c". d_forallp "n".
  d_splitp. d_swap. d_subst. d_eval.
  d_destructp (fun t => {A: ("n", "c") \in match: match: t with: {{(#, %, %) -> P 0 0}} with: {{(%, #) -> P 0 0}} }).
  d_orp.
  d_splitp. d_swap. d_subst. d_eval.
  d_rotate 4. d_subst. d_evalp.
  eapply DSCut; first by eapply DSNotImpliesFalse with (Ac := {A:
                                                                 CPair $ "n" $ "c" \in "r"}). d_swap. eapply DARewriteIffPL; first by d_head.
  rewrite_assertion_any. d_swap. d_clear. d_rotate 8.
  eapply DARewriteIfP with (Arp := {A: (CPair $ "n" $ "c" \in "r")})
                           (Arc := {A: AFalse}).
  d_rotate 3. d_head.
  rewrite_assertion_pos. d_false.

  d_splitp. d_clear.
  d_destructp (fun t => {A: ("n", "c") \in match: match: t with: {{(#, %, %) -> P 0 0}} with: {{(%, #) -> P 0 0}} }).
  d_splitp. d_swap. d_substp. d_evalp.
  d_swap. d_rotate 4. d_subst. d_evalp. d_swap.
  d_subst; d_eval.
  d_destructp (fun t => {A: ("Fs'" $ "n'", "Fors", "Fois") = t}).
  d_forallp "r". d_forallp "c'". d_splitp. d_swap. d_subst. d_eval.
  d_subst. d_evalp.
  d_destructtuplep
    {t: "Fs'" $ "n'"} {t: "Fors"} {t: "Fois"}
    {t: (CPair $ "c'" $ (FUnion $ "r" $ (CCons $ (CPair $ "n" $ "c") $ CNil)))}
    {t: CNil} {t: (CCons $ (CPLDeliver $ "n" $ "m") $ CNil)}.
  do 2 d_splitp.
  d_subst.
  d_existsc "m".
  d_splitc. d_splitc. eapply DAPEqual. by [].
  d_splitc. d_rotate 13.
  d_destructpairp {t: "i"} {t: "e"} {t: 0} {t: (CSLDeliver $ "n" $ (CPair $ "c" $ "m"))}.
  rewrite_assertion_any. d_splitp.
  d_subst. eapply DAPEqual. by [].
  d_splitc. by eapply DAPEqual.
  d_rotate 13.
  d_destructpairp {t: "i"} {t: "e"} {t: 0} {t: (CSLDeliver $ "n" $ (CPair $ "c" $ "m"))}.
  rewrite_assertion_any. d_splitp.
  d_subst. by eapply DAPEqual.
  eapply DAPIn. by []. by [].

  (* prove for periodic *)
  d_ifp. d_ifc. d_splitp. d_splitp. d_swap. d_splitp. d_rotate 3. d_subst. d_eval. d_splitp.
  d_destructtuplep
    {t: "Fs'" $ "n'"} {t: "Fors"} {t: "Fois"}
    {t: ("Fs" $ "n'")}
    {t: CNil} {t: CNil}.
  do 2 d_splitp. d_rotate 3. d_splitp. d_swap; d_subst. d_swap.
  eapply DSCut; first by eapply DSNotImpliesFalse with (Ac := {A:
                                                                 (CPair $ "n" $ "c" \in match: "Fs" $ "n'" with: {{(%, #) -> P 0 0}})}). d_swap. eapply DARewriteIffPL; first by d_head.
  rewrite_assertion_any. d_swap. d_clear. d_swap.
  eapply DARewriteIfP with (Arp := {A: (CPair $ "n" $ "c" \in match: "Fs" $ "n'" with: {{(%, #) -> P 0 0}})})
                           (Arc := {A: AFalse}).
  d_head.
  rewrite_assertion_pos. d_false.
  d_have {A:
            ("Fn" = "n'" /\  exists: "m"
                                      : ("Fn" = "n'" /\ "Fd" = CCons $ 0 $ CNil /\ "Fo" = OIndication /\ "Fe" = CSLDeliver $ "n" $ (CPair $ "c" $ "m")) /\
                                        CPLDeliver $ "n" $ "m" \in "Fois")
            ->
            ( exists: "m": "Fn" = "n'" /\ ("Fn" = "n'" /\ "Fd" = CCons $ 0 $ CNil /\ "Fo" = OIndication /\ "Fe" = CSLDeliver $ "n" $ (CPair $ "c" $ "m")) /\
                                        CPLDeliver $ "n" $ "m" \in "Fois")
         }.
  {
    d_ifc. d_splitp. d_existsc "m".
    d_splitc. d_head. d_clear. d_existsp "m".
    d_head.
  }
  d_swap. eapply DARewriteIfP; first by d_head.
  rewrite_assertion_pos.
  d_swap; d_clear.
  d_have {A:
            eventuallyp^ (exists: "m"
                                      : "Fn" = "n'" /\
                                        ("Fn" = "n'" /\ "Fd" = CCons $ 0 $ CNil /\ "Fo" = OIndication /\ "Fe" = CSLDeliver $ "n" $ (CPair $ "c" $ "m")) /\
                                        CPLDeliver $ "n" $ "m" \in "Fois")
            ->
            eventuallyp (exists: "m"
                                      : "Fn" = "n'" /\
                                        ("Fn" = "n'" /\ "Fd" = CCons $ 0 $ CNil /\ "Fo" = OIndication /\ "Fe" = CSLDeliver $ "n" $ (CPair $ "c" $ "m")) /\
                                        CPLDeliver $ "n" $ "m" \in "Fois")
         }.
  {
    d_ifc.
    d_right. d_head.
  }
  d_swap. eapply DARewriteIfP; first by d_head. rewrite_assertion_pos.

  set A := {A: ("Fn" = "n'" /\
                             ("Fn" = "n'" /\ "Fd" = CCons $ 0 $ CNil /\ "Fo" = OIndication /\ "Fe" = CSLDeliver $ "n" $ (CPair $ "c" $ "m")) /\
                             CPLDeliver $ "n" $ "m" \in "Fois")}.
  d_have {A:
            (eventuallyp exists: "m": A) <=> (exists: "m": eventuallyp A)}.

  eapply DTL127_3 with (A := {A: A})
                       (m := {t: "m"}).
  d_splitp. d_swap; d_clear.
  d_swap. eapply DARewriteEntailsP; first by d_head.
  rewrite_assertion_pos.
  d_have {A: A =>>
          (on "n'", event [0]<- CSLDeliver $ "n" $ (CPair $ "c" $ "m") /\ CPLDeliver $ "n" $ "m" \in "Fois")}.
  {
    eapply DTGeneralization; first by repeat constructor.
    d_ifc. d_splitp. d_splitc. d_splitc. d_head. d_clear. d_splitp.
    d_splitp.  d_clear. d_head.
    d_clear. d_splitp. d_swap. d_head.
  }
  d_swap. eapply DARewriteEntailsP; first by d_head. rewrite_assertion_pos.
  d_head.
Qed.

Lemma L40 :
  Context
    [:: V "c"; V "m"; V "n'"; V "n"; V "c'"; V "r"; V "r'"]
    [:: {A: correct "n"}; {A: correct "n'"}] |- perfect_link, {A:
    self-event /\ "Fn" = "n'" /\ ("n", "c") \in (FRight $ ("Fs" $ "n'")) =>>
    exists: "m": eventuallyp (
      on "n", ((0, CSLSend $ "n'" $ ("c", "m")) \in "Fors") /\
      self-event /\
      eventually on "n'", event []<- CPLDeliver $ "n" $ "m"
    )
    }.
Proof.
  set C := perfect_link.

  (* by Lemma 41 *)
  d_have {A:
            self-event /\ ("n", "c") \in (FRight $ ("Fs" $ "n'")) =>>
                                                                  exists: "m": eventuallyp (
                                                                                   on "n'", event [0]<- CSLDeliver $ "n" $ ("c", "m") /\ (CPLDeliver $ "n" $ "m" \in "Fois"))}.
  {
    apply L41.
  }

  (* by SL'2 *)
  d_have {A:

            on "n'", event [0]<- CSLDeliver $ "n" $ ("c", "m") =>>
                           eventuallyp on "n", event [0]-> CSLSend $ "n'" $ ("c", "m")}.
  {
    (* Use the lowering specification on SL_2 *)
    do 3 d_clear.
    d_have (derives_assertion PL_SL_2).
    d_clearv "r'"; d_clearv "r"; d_clearv "c'"; d_clearv "n"; d_clearv "n'"; d_clearv "m"; d_clearv "c".
    apply PL_SL_2.
    d_evalp.
    d_forallp "n'". d_forallp "n". d_forallp {t: ("c", "m")}.
    d_head.
  }

  (* by OR' *)
  d_have {A:
            on "n", event [0]-> CSLSend $ "n'" $ ("c", "m") =>>
                                        eventuallyp (self-event /\ on "n", ((0, CSLSend $ "n'" $ ("c", "m")) \in "Fors"))}.
  {
    d_use DPOR';
      d_forallp "n"; d_forallp 0; d_forallp {t: CSLSend $ "n'" $ ("c", "m")}.

      by eapply DARewriteIfP; first by apply DTL123 with (A := {A:
                                                                  self-event /\ on "n", ((0, CSLSend $ "n'" $ ("c", "m")) \in "Fors")}).
  }

  (* by Lemma 85 on [2] and [3] *)
  d_have {A:
            on "n'", event [0]<- CSLDeliver $ "n" $ ("c", "m") =>>
                           eventuallyp (self-event /\ on "n", ((0, CSLSend $ "n'" $ ("c", "m")) \in "Fors"))}.
  {
    eapply DTL85.
    - by d_rotate 1.
    - d_head.
  }

  (* by OI *)
  d_have {A:
            (on "n'", (self-event /\ (CPLDeliver $ "n" $ "m") \in "Fois")) =>>
                                                                           eventually (on "n'", (event []<- CPLDeliver $ "n" $ "m"))}.

  {
    d_use DPOI.
    d_forallp "n'". d_forallp {t: CPLDeliver $ "n" $ "m"}.

    eapply DARewriteIfP.
    apply DTL121 with (A := {A:
                               (on "n'", event []<- CPLDeliver $ "n" $ "m")}).
    rewrite_assertion_pos.
    d_subst.
    d_head.
  }

  (* by [1], [4], and [5] *)
  d_have {A:
            self-event /\ ("n", "c") \in (FRight $ ("Fs" $ "n'")) =>> exists: "m" :
                                                                  eventuallyp (
                                                                                   eventuallyp (self-event /\ on "n", ((0, CSLSend $ "n'" $ ("c", "m")) \in "Fors") ) /\
                                                                                   eventually (on "n'", (event []<- CPLDeliver $ "n" $ "m")))}.

  {
    d_rotate 4.
    d_have {A:
              (on "n'", event [0]<- CSLDeliver $ "n" $ (CPair $ "c" $ "m") /\ CPLDeliver $ "n" $ "m" \in "Fois") ->
              (on "n'", event [0]<- CSLDeliver $ "n" $ (CPair $ "c" $ "m") /\ (on "n'", (self-event /\ CPLDeliver $ "n" $ "m" \in "Fois")))}.
    d_ifc.
    d_splitc. d_splitp. d_head.
    d_use DPSecondIndicationSelf. d_forallp {t: CSLDeliver $ "n" $ (CPair $ "c" $ "m")}.
    d_splitp. d_swap; d_clear.
    d_ifp. d_splitp. d_splitp. d_swap. d_head.
    d_splitc. d_swap. d_splitp. d_splitp. d_head.
    d_splitc. d_head.
    d_swap. d_splitp. d_swap. d_head.

    d_swap.

    eapply DARewriteIfP with (Arp := {A:
                                        (on "n'", event [0]<- CSLDeliver $ "n" $ (CPair $ "c" $ "m") /\ CPLDeliver $ "n" $ "m" \in "Fois")})
                             (Arc := {A:
                                        (on "n'", event [0]<- CSLDeliver $ "n" $ (CPair $ "c" $ "m") /\ on "n'", (self-event /\ CPLDeliver $ "n" $ "m" \in "Fois"))}).
    d_head.
    rewrite_assertion_pos.

    eapply DARewriteEntailsP with (Arp := {A:
                                             on "n'", (self-event /\ CPLDeliver $ "n" $ "m" \in "Fois")})
                                  (Arc := {A:
                                             eventually (on "n'", event []<- CPLDeliver $ "n" $ "m")}).
    d_rotate 3. d_head.
    rewrite_assertion_pos.

    eapply DARewriteEntailsP with (Arp := {A:
                                             ("Fn" = "n'" /\ "Fd" = CCons $ 0 $ CNil /\ "Fo" = OIndication /\ "Fe" = CSLDeliver $ "n" $ (CPair $ "c" $ "m"))})
                                  (Arc := {A:
                                             eventuallyp (self-event /\ on "n", (CPair $ 0 $ (CSLSend $ "n'" $ (CPair $ "c" $ "m")) \in "Fors"))}).
    d_rotate 4. d_head.
    rewrite_assertion_pos.

    d_head.
  }

  eapply DARewriteIfP with (Arp := {A: (self-event) /\ (("Fn" = "n" /\ CPair $ 0 $ (CSLSend $ "n'" $ (CPair $ "c" $ "m")) \in "Fors"))})
                           (Arc := {A: (("Fn" = "n" /\ CPair $ 0 $ (CSLSend $ "n'" $ (CPair $ "c" $ "m")) \in "Fors") /\ (self-event))}).
  d_ifc.
  d_splitp. d_splitc.
  d_swap. d_head. d_head.

  rewrite_assertion_pos.

  set A1 := {A: ("Fn" = "n" /\ CPair $ 0 $ (CSLSend $ "n'" $ (CPair $ "c" $ "m")) \in "Fors")}.
  set A2 := {A: ("Fn" = "n'" /\ "Fd" = CNil /\ "Fo" = OIndication /\ "Fe" = CPLDeliver $ "n" $ "m")}.

  eapply DARewriteEntailsP with (Arp := {A: eventuallyp (A1 /\ self-event) /\ eventually A2})
                                (Arc := {A: eventuallyp ((A1 /\ self-event) /\ eventually A2)}).
  eapply DTL102_3 with (A1 := {A: (A1 /\ self-event)})
                       (A2 := {A: A2}).
  rewrite_assertion_pos.
  eapply DARewriteCongruentPR with (Arp := {A: eventuallyp ((A1 /\ self-event) /\ eventually A2)})
                                   (Arc := {A: eventuallyp (eventuallyp ((A1 /\ self-event) /\ eventually A2))}).
  eapply DTL83_1.
  rewrite_assertion_any.

  (* take care of the right associativity of /\ *)
  d_have {A:
            ((A1 /\ self-event) /\ eventually A2) ->
            (A1 /\ (self-event /\ eventually A2))}.

  {
    d_ifc.
    d_splitc. d_splitp. d_splitp. d_head.
    d_splitp. d_splitc. d_splitp. d_swap. d_head.
    d_swap. d_head.
  }
  d_swap.
  eapply DARewriteIfP with (Arp := {A: (A1 /\ self-event) /\ eventually A2})
                           (Arc := {A: A1 /\ self-event /\ eventually A2}).
  d_head.
  rewrite_assertion_pos.

  d_have {A:
            (self-event /\ "Fn" = "n'" /\ CPair $ "n" $ "c" \in FRight $ ("Fs" $ "n'")) =>>
                                                                         self-event /\ CPair $ "n" $ "c" \in FRight $ ("Fs" $ "n'")
         }.
  {
    eapply DTGeneralization; first by repeat constructor.
    d_ifc. d_splitc. d_splitp; first by d_head.
    d_splitp. d_swap. d_splitp; d_swap.
    d_head.
  }
  eapply DTL77 with (A1 := {A: self-event /\ "Fn" = "n'" /\ CPair $ "n" $ "c" \in FRight $ ("Fs" $ "n'")})
                    (A2 := {A: self-event /\ CPair $ "n" $ "c" \in FRight $ ("Fs" $ "n'")})
                    (A3 := {A: exists: "m" : eventuallyp (on "n", (CPair $ 0 $ (CSLSend $ "n'" $ (CPair $ "c" $ "m")) \in "Fors") /\ self-event /\ eventually on "n'", event []<- CPLDeliver $ "n" $ "m")}).
  d_head.
  d_swap.
  d_head.
Qed.

Lemma L38 :
  Context
    [:: V "c"; V "m"; V "n'"; V "n"; V "c'"; V "r"; V "r'"]
    [:: {A: correct "n"}; {A: correct "n'"}] |- perfect_link, {A:
    on "n'", event [0]<- CSLDeliver $ "n" $ ("c", "m") =>>
    eventually on "n'", event []<- CPLDeliver $ "n" $ "m" \/
                        exists: "m": (eventuallyp ((on "n", self-event /\ (0, CSLSend $ "n'" $ ("c", "m")) \in "Fors") /\ eventually on "n'", event []<- CPLDeliver $ "n" $ "m"))
                                                              }.
Proof.
  d_use L39.

  d_have {A:
            self-event /\ "Fn" = "n'" /\ ("n", "c") \in (FRight $ ("Fs" $ "n'")) =>>
                                                                                 exists: "m": eventuallyp (
                                                                                                  (on "n", ((0, CSLSend $ "n'" $ ("c", "m")) \in "Fors") /\
                                                                                                          self-event) /\
                                                                                                          eventually on "n'", event []<- CPLDeliver $ "n" $ "m"
         )}.
  {
    d_clear.
    d_use L40.
    d_have {A:
              (on "n", (CPair $ 0 $ (CSLSend $ "n'" $ (CPair $ "c" $ "m")) \in "Fors") /\ self-event /\ eventually on "n'", event []<- CPLDeliver $ "n" $ "m") ->
              ((on "n", (CPair $ 0 $ (CSLSend $ "n'" $ (CPair $ "c" $ "m")) \in "Fors") /\ self-event) /\ eventually on "n'", event []<- CPLDeliver $ "n" $ "m")}.
    {
      d_ifc. d_splitp. d_splitc. d_splitc. d_head.
      d_swap. d_splitp. d_head. d_swap. d_splitp. d_swap. d_head.
    }
    d_swap.
    eapply DARewriteIfP; first by d_head. rewrite_assertion_pos.
    d_head.
  }

  d_have {A:
            on "n'", event [0]<- CSLDeliver $ "n" $ ("c", "m") /\ ("n", "c") \in (FRight $ ("Fs" $ "n'")) =>>
                                                                                                self-event /\ "Fn" = "n'" /\ ("n", "c") \in (FRight $ ("Fs" $ "n'"))}.
  {
    eapply DTGeneralization; first by repeat constructor.
    d_ifc.
    d_splitc. d_splitp.
    d_use DPSecondIndicationSelf.
    d_forallp {t: CSLDeliver $ "n" $ (CPair $ "c" $ "m")}.
    eapply DARewriteEntailsC; first by d_head.
    rewrite_assertion_pos.
    d_clear. d_splitp. d_swap. d_head.
    d_splitp. d_splitp. d_splitc. d_head.
    d_rotate 2. d_head.
  }
  eapply DARewriteEntailsP; first by d_head. rewrite_assertion_pos.

  d_have {A:
            (on "n", (CPair $ 0 $ (CSLSend $ "n'" $ (CPair $ "c" $ "m")) \in "Fors") /\ self-event ) =>>
                                                                                                     (on "n", self-event /\ CPair $ 0 $ (CSLSend $ "n'" $ (CPair $ "c" $ "m")) \in "Fors")
         }.
  {
    eapply DTGeneralization; first by repeat constructor.
    d_ifc.
    d_splitp. d_splitp.
    d_splitc. d_splitc. d_head.
    d_rotate 2. d_head.
    d_swap. d_head.
  }
  d_swap.
  eapply DARewriteEntailsP; first by d_head. rewrite_assertion_pos.

  set A := {A: on "n'", event [0]<- CSLDeliver $ "n" $ ("c", "m")}.
  set B := {A: ("n", "c") \notin (FRight $ ("Fs" $ "n'"))}.
  set D := {A: ("n", "c") \in (FRight $ ("Fs" $ "n'"))}.
  d_have {A:
            A =>> A /\ (B \/ D)
         }.
  {
    eapply DTGeneralization; first by repeat constructor.
    d_ifc. d_splitc. d_head.
    d_eval.
    d_ifc.
    d_head.
  }

  eapply DARewriteIffPL with (Arp := {A:  A /\ (B \/ D)})
                            (Arc := {A: (A /\ B) \/ (A /\ D)}).
  eapply DSOrDistributesAnd with (A := {A: A})
                                 (Al := {A: B})
                                 (Ar := {A: D}).
  rewrite_assertion_any.
  eapply DARewriteEntailsP with (Arp := {A: A /\ B})
                                (Arc := {A: eventually on "n'", event []<- CPLDeliver $ "n" $ "m"}).
  d_rotate 3. d_head.
  rewrite_assertion_pos.
  eapply DARewriteEntailsP with (Arp := {A: A /\ D})
                                (Arc := {A: exists: "m"
                                                  : eventuallyp ((on "n", self-event /\ CPair $ 0 $ (CSLSend $ "n'" $ (CPair $ "c" $ "m")) \in "Fors") /\
                                       eventually ("Fn" = "n'" /\ "Fd" = CNil /\ "Fo" = OIndication /\ "Fe" = CPLDeliver $ "n" $ "m"))}).
  d_head. rewrite_assertion_pos.
  d_head.
Qed.

(* Reliable delivery
 * If a correct node n sends a message m to a correct node n', then n' will
 * eventually deliver m.
 *)
Theorem PL_1 : Context [:: V "m'"; V "c"; V "m"; V "n'"; V "n"; V "c'"; V "r"; V "r'"] [::] |- perfect_link, {A:
  correct "n" /\ correct "n'" ->
  on "n", event []-> CPLSend $ "n'" $ "m" ~>
  on "n'", event []<- CPLDeliver $ "n" $ "m"
}.
Proof.
  (* Introduce context *)
  set C := perfect_link.
  d_ifc; d_splitp.

  (* by IR *)
  d_have {A:
            on "n", event []-> CPLSend $ "n'" $ "m" =>>
                                       exists: "c": self-event /\ on "n", ((0, CSLSend $ "n'" $ ("c", "m")) \in "Fors")
         }.
  {
    eapply DTGeneralization; first by repeat constructor.
    d_ifc.

    (* self case *)
    d_existsc {t: FSucc $ "c"}.
    d_splitc.
    d_subst.
    d_ifc.
    d_left.
    d_swap. do 2 (d_splitp; d_swap).
    d_swap.
    d_splitc. d_head.
    d_swap; d_splitp; d_head.

    d_use DPIR.
    d_forallp {t: CPLSend $ "n'" $ "m"}. d_evalp.
    d_splitp. d_swap. d_clear.
    d_ifp. d_subst.
    d_splitp. d_swap.
    d_head.

    d_destructp (fun t => {A: ("Fs'" $ "Fn", "Fors", "Fois") = t}).
    d_forallp "r"; d_forallp "c".
    d_splitp. d_swap.
    d_substp. d_evalp.
    d_destructtuplep
      {t: "Fs'" $ "Fn"} {t: "Fors"} {t: "Fois"}
      {t: (FSucc $ "c", "r")}
      {t: (CCons $ (CPair $ 0 $ (CSLSend $ "n'" $ (CPair $ (FSucc $ "c") $ "m"))) $ CNil)} {t: CNil}; do 2 d_splitp.
    d_subst. d_splitc.
    d_rotate 4. d_substp. d_splitp. d_head.
    eapply DAPIn. by []. by [].
  }
  d_have {A:
            (exists: "c": (self-event /\ on "n", ((0, CSLSend $ "n'" $ ("c", "m")) \in "Fors"))) ->
                                               self-event /\ on "n", ((0, CSLSend $ "n'" $ ("c", "m")) \in "Fors")
         }.
  {
    d_ifc.
    d_existsp "c".
    d_head.
  }
  d_swap.
  eapply DARewriteIfP with (Arp := {A: (exists: "c"
                                              : self-event /\ on "n", (CPair $ 0 $ (CSLSend $ "n'" $ (CPair $ "c" $ "m")) \in "Fors"))})
                           (Arc := {A: self-event /\ on "n", (CPair $ 0 $ (CSLSend $ "n'" $ (CPair $ "c" $ "m")) \in "Fors")}).
  d_head.
  rewrite_assertion_pos.
  d_swap; d_clear.

  (* by OR *)
  d_have {A:
            (self-event /\ on "n", ((0, CSLSend $ "n'" $ ("c", "m")) \in "Fors")) =>>
                                                                                eventually (on "n", event[0]-> CSLSend $ "n'" $ ("c", "m"))
         }.
  {
    d_use DPOR.
    d_forallp "n". d_forallp 0. d_forallp {t: CSLSend $ "n'" $ ("c", "m")}.
    eapply DARewriteIfP. apply DTL121 with (A := {A:
          ("Fn" = "n" /\ "Fd" = CCons $ 0 $ CNil /\ "Fo" = ORequest /\ "Fe" = CSLSend $ "n'" $ (CPair $ "c" $ "m"))}).
    rewrite_assertion_pos.
    d_swap; d_clear.
    (* need to move "Fn" = "n" *)
    d_have {A:
              self-event /\ "Fn" = "n" /\ CPair $ 0 $ (CSLSend $ "n'" $ (CPair $ "c" $ "m")) \in "Fors" =>>
                                                                                                 "Fn" = "n" /\ self-event /\
                                                                                                 CPair $ 0 $ (CSLSend $ "n'" $ (CPair $ "c" $ "m")) \in "Fors"}.
    {
      eapply DTGeneralization; first by repeat constructor.
      d_ifc. d_splitc. d_splitp. d_swap. d_splitp. d_head.
      d_splitc. d_splitp. d_head.
      do 2 (d_splitp; d_swap). d_head.
    }

    d_swap.
    d_swap.
    eapply DTL77 with (A1 := {A: (self-event /\ "Fn" = "n" /\ CPair $ 0 $ (CSLSend $ "n'" $ (CPair $ "c" $ "m")) \in "Fors")})
                      (A2 := {A: ("Fn" = "n" /\ self-event /\ CPair $ 0 $ (CSLSend $ "n'" $ (CPair $ "c" $ "m")) \in "Fors")})
                      (A3 := {A: eventually ("Fn" = "n" /\ "Fd" = CCons $ 0 $ CNil /\ "Fo" = ORequest /\ "Fe" = CSLSend $ "n'" $ (CPair $ "c" $ "m"))}).
    d_head.
    d_swap.
    d_head.
  }

  (* apply DTL96 on above assumptions *)
  d_have {A:
            on "n", event []-> CPLSend $ "n'" $ "m" ~>
                                       on "n", event [0]-> CSLSend $ "n'" $ (CPair $ "c" $ "m")
         }.

  {
    d_swap.
    set A := {A: self-event /\ on "n", (CPair $ 0 $ (CSLSend $ "n'" $ (CPair $ "c" $ "m")) \in "Fors")}.
    set B := {A: "Fn" = "n" /\ "Fd" = CCons $ 0 $ CNil /\ "Fo" = ORequest /\ "Fe" = CSLSend $ "n'" $ (CPair $ "c" $ "m")}.
    set D := {A: on "n", event []-> CPLSend $ "n'" $ "m"}.

    (* d_head cannot resolve the goal eventhough the assumption and goal are identical *)
    (* d_existsc "c" doesn't work here because it works for both premis and conclusion part*)
    (* a workaround is to break down the assertion into pieces and match them one by one *)
    (* Unset Printing Notations. *)

    eapply DTL77 with (A1 := {A: on "n", event []-> CPLSend $ "n'" $ "m"})
                      (A2 := {A: self-event /\ on "n", (CPair $ 0 $ (CSLSend $ "n'" $ (CPair $ "c" $ "m")) \in "Fors")})
                      (A3 := {A: eventually (on "n", event [0]-> CSLSend $ "n'" $ (CPair $ "c" $ "m"))}).
    eapply DTGeneralization; first by repeat constructor.
    d_ifc. d_swap. d_splitp; d_swap; d_clear. d_ifp. d_head.
    d_head.
    d_swap.
    d_head.
  }

  (* by SL'1 and Axiom 1 *)
  d_have {A:
            on "n", event[0]-> CSLSend $ "n'" $ ("c", "m") =>>
                                       eventually (on "n'", event[0]<- CSLDeliver $ "n" $ ("c", "m"))
         }.
  {
    d_have {A:
              forall: "n0", "n0'", "m0":
                                   correct "n0" /\ correct "n0'" ->
                                   on "n0", event [0]-> CSLSend $ "n0'" $ "m0" =>>
                                                               always eventually on "n0'", event [0]<- CSLDeliver $ "n0" $ "m0"}.
    {
      do 5 d_clear.
      d_clearv "r'"; d_clearv "r"; d_clearv "c'"; d_clearv "n"; d_clearv "n'"; d_clearv "m"; d_clearv "c"; d_clearv "m'".
      eapply PL_SL_1.
    }
    d_forallp "n"; d_forallp "n'"; d_forallp {t: ("c", "m")}.

    d_ifp.
    d_splitc. d_rotate 3. d_head. d_rotate 4. d_head.

    eapply DARewriteIfP; first by apply DT1 with (A := {A:
                                                       eventually on "n'", event [0]<- CSLDeliver $ "n" $ (CPair $ "c" $ "m")}).
    rewrite_assertion_pos.
    d_head.
  }

  (* by Lemma 86 on [1] and [2] *)
  d_have {A:
            on "n", event[]-> CPLSend $ "n'" $ "m" =>>
                                      (eventually (on "n'", event[0]<- CSLDeliver $ "n" $ ("c", "m")))}.
  {
    eapply DTL86 with (A1 := {A: on "n", event []-> CPLSend $ "n'" $ "m"})
                      (A2 := {A: on "n", event [0]-> CSLSend $ "n'" $ (CPair $ "c" $ "m")})
                      (A3 := {A: on "n'", event [0]<- CSLDeliver $ "n" $ (CPair $ "c" $ "m")}).
    d_swap; first by d_head.
    d_head.
  }

  d_have {A:
            on "n", event[]-> CPLSend $ "n'" $ "m" =>>
                                      (self-event /\ on "n", (CPair $ 0 $ (CSLSend $ "n'" $ (CPair $ "c" $ "m")) \in "Fors")) /\ (eventually on "n'", event [0]<- CSLDeliver $ "n" $ (CPair $ "c" $ "m"))}.
  {
    eapply DARewriteIffCR with (Arc := {A: (on "n", event []-> CPLSend $ "n'" $ "m") -> ((self-event /\ on "n", (CPair $ 0 $ (CSLSend $ "n'" $ (CPair $ "c" $ "m")) \in "Fors")) /\ (eventually on "n'", event [0]<- CSLDeliver $ "n" $ (CPair $ "c" $ "m")))})
                               (Arp := {A: ((on "n", event []-> CPLSend $ "n'" $ "m") -> (self-event /\ on "n", (CPair $ 0 $ (CSLSend $ "n'" $ (CPair $ "c" $ "m")) \in "Fors"))) /\
                                           ((on "n", event []-> CPLSend $ "n'" $ "m") -> (eventually on "n'", event [0]<- CSLDeliver $ "n" $ (CPair $ "c" $ "m")))}).
    eapply DSIfAndSplit with (Ap := {A: on "n", event []-> CPLSend $ "n'" $ "m"})
                             (Acl := {A: (self-event /\ on "n", (CPair $ 0 $ (CSLSend $ "n'" $ (CPair $ "c" $ "m")) \in "Fors"))})
                             (Acr := {A: eventually on "n'", event [0]<- CSLDeliver $ "n" $ (CPair $ "c" $ "m")}).
    rewrite_assertion_any.
    set A := {A: (on "n", event []-> CPLSend $ "n'" $ "m" -> self-event /\ on "n", (CPair $ 0 $ (CSLSend $ "n'" $ (CPair $ "c" $ "m")) \in "Fors"))}.
    set B := {A: (on "n", event []-> CPLSend $ "n'" $ "m" -> eventually on "n'", event [0]<- CSLDeliver $ "n" $ (CPair $ "c" $ "m"))}.

    eapply DARewriteCongruentCL with (Arp := {A: always (A /\ B)})
                                     (Arc := {A: (always A) /\ (always B)}).
    eapply DTL128_1.
    rewrite_assertion_any.
    d_splitc.
    d_rotate 4. d_head.
    d_head.
  }

  (* by Lemma 96 on [3] and Lemma 38 *)
  d_have {A:
            on "n", event[]-> CPLSend $ "n'" $ "m" =>>
                                      (self-event /\ (on "n", ((0, CSLSend $ "n'" $ ("c", "m")) \in "Fors"))) /\
                              eventually ((eventually (on "n'", event[]<- CPLDeliver $ "n" $ "m")) \/
                                          exists: "m": (eventuallyp ((self-event /\ "Fn" = "n" /\ ((0, CSLSend $ "n'" $ ("c", "m")) \in "Fors")) /\ (eventually (on "n'", event[]<- CPLDeliver $ "n" $ "m")))))
         }.
  {

    set B := {A: (eventually (on "n'", event[]<- CPLDeliver $ "n" $ "m"))}.
    eapply DARewriteEntailsP with (Arp := {A: on "n'", event [0]<- CSLDeliver $ "n" $ ("c", "m")})
                                  (Arc := {A: B \/
                        exists: "m": (eventuallyp ((on "n", self-event /\ (0, CSLSend $ "n'" $ ("c", "m")) \in "Fors") /\ B))}).
    do 5 d_clear. d_clearv "m'".
    eapply L38.
    rewrite_assertion_pos.

    d_have {A:
              ((on "n", self-event /\ CPair $ 0 $ (CSLSend $ "n'" $ (CPair $ "c" $ "m")) \in "Fors") /\ eventually on "n'", event []<- CPLDeliver $ "n" $ "m") ->
              ((self-event /\ "Fn" = "n" /\ CPair $ 0 $ (CSLSend $ "n'" $ (CPair $ "c" $ "m")) \in "Fors") /\ eventually on "n'", event []<- CPLDeliver $ "n" $ "m")}.
    {
      d_ifc. d_splitp. d_splitp. d_splitc.
      d_splitc. d_splitp.
      d_swap; first by d_head.
      d_splitc. d_splitp; first by d_head. d_swap.
      d_head.
      d_rotate 2; first by d_head.
    }
    d_swap.
    eapply DARewriteIfP with (Arp := {A: (on "n", self-event /\ CPair $ 0 $ (CSLSend $ "n'" $ (CPair $ "c" $ "m")) \in "Fors") /\ eventually on "n'", event []<- CPLDeliver $ "n" $ "m"})
                             (Arc := {A: (self-event /\ "Fn" = "n" /\ CPair $ 0 $ (CSLSend $ "n'" $ (CPair $ "c" $ "m")) \in "Fors") /\ eventually on "n'", event []<- CPLDeliver $ "n" $ "m"}).
    d_head.
    rewrite_assertion_pos.

    d_head.
  }

  d_have {A:
            on "n", event[]-> CPLSend $ "n'" $ "m" =>>
                                      (self-event /\ "Fn" = "n" /\ (0, CSLSend $ "n'" $ ("c", "m")) \in "Fors") /\
                              ((eventually (eventually (on "n'", event[]<- CPLDeliver $ "n" $ "m"))) \/
                                         (eventually (exists: "m": eventuallyp ((self-event /\ "Fn" = "n" /\ (0, CSLSend $ "n'" $ ("c", "m")) \in "Fors") /\ eventually (on "n'", event[]<- CPLDeliver $ "n" $ "m")))))
         }.
  {
    set A := {A: exists: "m" : eventuallyp ((self-event /\ "Fn" = "n" /\ CPair $ 0 $ (CSLSend $ "n'" $ (CPair $ "c" $ "m")) \in "Fors") /\ (eventually on "n'", event []<- CPLDeliver $ "n" $ "m"))}.
    set B := {A: eventually (on "n'", event[]<- CPLDeliver $ "n" $ "m")}.

    eapply DARewriteCongruentPL with (Arp := {A: eventually (B \/ A)})
                                     (Arc := {A: (eventually B) \/ (eventually A)}).
    eapply DTL127_1.
    rewrite_assertion_any.

    d_head.
  }

  d_have {A:
            on "n", event[]-> CPLSend $ "n'" $ "m" =>>
                                      (self-event /\ "Fn" = "n" /\ (0, CSLSend $ "n'" $ ("c", "m")) \in "Fors") /\
                              ((eventually (on "n'", event[]<- CPLDeliver $ "n" $ "m")) \/
                               (exists: "m": eventually (eventuallyp ((self-event /\ "Fn" = "n" /\ ((0, CSLSend $ "n'" $ ("c", "m")) \in "Fors")) /\ eventually (on "n'", event[]<- CPLDeliver $ "n" $ "m")))))
         }.
  {
    d_subst.
    set A1 := {A: (self-event /\ "Fn" = "n" /\ CPair $ 0 $ (CSLSend $ "n'" $ (CPair $ "c" $ "m")) \in "Fors")}.
    set A2 := {A: ((self-event /\ "Fn" = "n" /\ CPair $ 0 $ (CSLSend $ "n'" $ (CPair $ "c" $ "m")) \in "Fors") /\ (eventually on "n'", event []<- CPLDeliver $ "n" $ "m"))}.
    set B1 := {A: eventually eventually (on "n'", event[]<- CPLDeliver $ "n" $ "m")}.
    set B2 := {A: eventually (on "n'", event[]<- CPLDeliver $ "n" $ "m")}.

    eapply DARewriteCongruentPR with (Arc := {A: eventually eventually on "n'", event []<- CPLDeliver $ "n" $ "m"})
                                     (Arp := {A: eventually on "n'", event []<- CPLDeliver $ "n" $ "m"}).
    eapply DTL84 with (A := {A: on "n'", event []<- CPLDeliver $ "n" $ "m"}).
    rewrite_assertion_any.

    d_subst.
    set A3 := {A: (self-event /\ "Fn" = "n" /\ CPair $ 0 $ (CSLSend $ "n'" $ (CPair $ "c" $ "m")) \in "Fors")}.
    set A4 := {A: ((self-event /\ "Fn" = "n" /\ CPair $ 0 $ (CSLSend $ "n'" $ (CPair $ "c" $ "m")) \in "Fors") /\ (eventually on "n'", event []<- CPLDeliver $ "n" $ "m"))}.
    set B3 := {A: eventually eventually (on "n'", event[]<- CPLDeliver $ "n" $ "m")}.
    set B4 := {A: eventually (on "n'", event[]<- CPLDeliver $ "n" $ "m")}.

    eapply DARewriteCongruentPL with (Arp := {A: eventually (exists: "m": eventuallyp A4)})
                                     (Arc := {A: (exists: "m": (eventually eventuallyp A4))}).
    eapply DTL127_2 with (A := {A: eventuallyp A4})
                         (m := {t: "m"}).
    rewrite_assertion_any.
    d_head.
  }

  d_have {A:
            on "n", event[]-> CPLSend $ "n'" $ "m" =>>
                                      (self-event /\ "Fn" = "n" /\ (0, CSLSend $ "n'" $ ("c", "m")) \in "Fors") /\
                              ((eventually (on "n'", event[]<- CPLDeliver $ "n" $ "m")) \/
                               (exists: "m": ((eventually^ ((self-event /\ "Fn" = "n" /\ ((0, CSLSend $ "n'" $ ("c", "m")) \in "Fors")) /\ eventually (on "n'", event[]<- CPLDeliver $ "n" $ "m"))) \/
                                              ((self-event /\ "Fn" = "n" /\ ((0, CSLSend $ "n'" $ ("c", "m")) \in "Fors")) /\ eventually (on "n'", event[]<- CPLDeliver $ "n" $ "m")) \/
                              (eventuallyp^ ((self-event /\ "Fn" = "n" /\ ((0, CSLSend $ "n'" $ ("c", "m")) \in "Fors")) /\ eventually (on "n'", event[]<- CPLDeliver $ "n" $ "m"))))))
         }.
  {
    set A1 := {A: (self-event /\ "Fn" = "n" /\ CPair $ 0 $ (CSLSend $ "n'" $ (CPair $ "c" $ "m")) \in "Fors")}.
    set A2 := {A: ((self-event /\ "Fn" = "n" /\ CPair $ 0 $ (CSLSend $ "n'" $ (CPair $ "c" $ "m")) \in "Fors") /\ (eventually on "n'", event []<- CPLDeliver $ "n" $ "m"))}.
    set B1 := {A: eventually (on "n'", event[]<- CPLDeliver $ "n" $ "m")}.

    eapply DARewriteEntailsP with (Arp := {A: eventually eventuallyp A2})
                                  (Arc := {A: eventually^ A2 \/ A2 \/ eventuallyp^ A2}).
    eapply DTL109_3_a.
    rewrite_assertion_pos.
    d_head.
  }

  d_have {A:
            (exists: "m": ((eventually^ ((self-event /\ "Fn" = "n" /\ ((0, CSLSend $ "n'" $ ("c", "m")) \in "Fors")) /\ eventually (on "n'", event[]<- CPLDeliver $ "n" $ "m"))) \/ ((self-event /\ "Fn" = "n" /\ ((0, CSLSend $ "n'" $ ("c", "m")) \in "Fors")) /\ eventually (on "n'", event[]<- CPLDeliver $ "n" $ "m")) \/
                           (eventuallyp^ ((self-event /\ "Fn" = "n" /\ ((0, CSLSend $ "n'" $ ("c", "m")) \in "Fors")) /\ eventually (on "n'", event[]<- CPLDeliver $ "n" $ "m"))))) ->
            ((eventually^ ((self-event /\ "Fn" = "n" /\ ((0, CSLSend $ "n'" $ ("c", "m'")) \in "Fors")) /\ eventually (on "n'", event[]<- CPLDeliver $ "n" $ "m'"))) \/ ((self-event /\ "Fn" = "n" /\ ((0, CSLSend $ "n'" $ ("c", "m")) \in "Fors")) /\ eventually (on "n'", event[]<- CPLDeliver $ "n" $ "m")) \/
             (eventuallyp^ ((self-event /\ "Fn" = "n" /\ ((0, CSLSend $ "n'" $ ("c", "m'")) \in "Fors")) /\ eventually (on "n'", event[]<- CPLDeliver $ "n" $ "m'"))))
         }.
  {
    d_have {A:
              (exists: "m": ((eventually^ ((self-event /\ "Fn" = "n" /\ ((0, CSLSend $ "n'" $ ("c", "m")) \in "Fors")) /\ eventually (on "n'", event[]<- CPLDeliver $ "n" $ "m"))) \/ ((self-event /\ "Fn" = "n" /\ ((0, CSLSend $ "n'" $ ("c", "m")) \in "Fors")) /\ eventually (on "n'", event[]<- CPLDeliver $ "n" $ "m")) \/
                             (eventuallyp^ ((self-event /\ "Fn" = "n" /\ ((0, CSLSend $ "n'" $ ("c", "m")) \in "Fors")) /\ eventually (on "n'", event[]<- CPLDeliver $ "n" $ "m")))))
              ->
              (exists: "m": (eventually^ ((self-event /\ "Fn" = "n" /\ ((0, CSLSend $ "n'" $ ("c", "m")) \in "Fors")) /\ eventually (on "n'", event[]<- CPLDeliver $ "n" $ "m")))) \/ (exists: "m": ((self-event /\ "Fn" = "n" /\ ((0, CSLSend $ "n'" $ ("c", "m")) \in "Fors")) /\ eventually (on "n'", event[]<- CPLDeliver $ "n" $ "m"))) \/
                             (exists: "m": eventuallyp^ ((self-event /\ "Fn" = "n" /\ ((0, CSLSend $ "n'" $ ("c", "m")) \in "Fors")) /\ eventually (on "n'", event[]<- CPLDeliver $ "n" $ "m")))}.
    {
      set A1 := {A: eventually^ ((self-event /\ "Fn" = "n" /\ CPair $ 0 $ (CSLSend $ "n'" $ (CPair $ "c" $ "m")) \in "Fors") /\ eventually on "n'", event []<- CPLDeliver $ "n" $ "m")}.
      set A2 := {A: ((self-event /\ "Fn" = "n" /\ ((0, CSLSend $ "n'" $ ("c", "m")) \in "Fors")) /\ eventually (on "n'", event[]<- CPLDeliver $ "n" $ "m"))}.
      set A3 := {A: (eventuallyp^ ((self-event /\ "Fn" = "n" /\ ((0, CSLSend $ "n'" $ ("c", "m")) \in "Fors")) /\ eventually (on "n'", event[]<- CPLDeliver $ "n" $ "m")))}.
      d_ifc.
      eapply DARewriteIffPL with (Arp := {A: (exists: "m" : (A1 \/ A2 \/ A3))})
                                 (Arc := {A:  ((exists: "m": A1) \/ (exists: "m": A2) \/ (exists: "m": A3))}).

      eapply DSExistsDistributesOr3 with (A1 := {A: A1})
                                         (A2 := {A: A2})
                                         (A3 := {A: A3})
                                         (x := {t: "m"}).
      rewrite_assertion_any.
      d_head.
    }
    d_ifc.
    set A1 := {A: eventually^ ((self-event /\ "Fn" = "n" /\ CPair $ 0 $ (CSLSend $ "n'" $ (CPair $ "c" $ "m")) \in "Fors") /\ eventually on "n'", event []<- CPLDeliver $ "n" $ "m")}.
    set A2 := {A: ((self-event /\ "Fn" = "n" /\ ((0, CSLSend $ "n'" $ ("c", "m")) \in "Fors")) /\ eventually (on "n'", event[]<- CPLDeliver $ "n" $ "m"))}.
    set A3 := {A: (eventuallyp^ ((self-event /\ "Fn" = "n" /\ ((0, CSLSend $ "n'" $ ("c", "m")) \in "Fors")) /\ eventually (on "n'", event[]<- CPLDeliver $ "n" $ "m")))}.
    eapply DARewriteIfP with (Arp := {A: (exists: "m" : (A1 \/ A2 \/ A3))})
                             (Arc:= {A: ((exists: "m": A1) \/ (exists: "m": A2) \/ (exists: "m": A3))}).
    d_head. rewrite_assertion_pos.
    d_orp. d_left. d_existsp "m'". d_head.
    d_orp. d_right. d_left. d_existsp "m". d_head.
    d_existsp "m'". d_right. d_right. d_head.
  }
  d_swap.
  eapply DARewriteIfP with (Arp := {A: (exists: "m": ((eventually^ ((self-event /\ "Fn" = "n" /\ ((0, CSLSend $ "n'" $ ("c", "m")) \in "Fors")) /\ eventually (on "n'", event[]<- CPLDeliver $ "n" $ "m"))) \/ ((self-event /\ "Fn" = "n" /\ ((0, CSLSend $ "n'" $ ("c", "m")) \in "Fors")) /\ eventually (on "n'", event[]<- CPLDeliver $ "n" $ "m")) \/
                           (eventuallyp^ ((self-event /\ "Fn" = "n" /\ ((0, CSLSend $ "n'" $ ("c", "m")) \in "Fors")) /\ eventually (on "n'", event[]<- CPLDeliver $ "n" $ "m")))))})
                           (Arc := {A: ((eventually^ ((self-event /\ "Fn" = "n" /\ ((0, CSLSend $ "n'" $ ("c", "m'")) \in "Fors")) /\ eventually (on "n'", event[]<- CPLDeliver $ "n" $ "m'"))) \/ ((self-event /\ "Fn" = "n" /\ ((0, CSLSend $ "n'" $ ("c", "m")) \in "Fors")) /\ eventually (on "n'", event[]<- CPLDeliver $ "n" $ "m")) \/
                           (eventuallyp^ ((self-event /\ "Fn" = "n" /\ ((0, CSLSend $ "n'" $ ("c", "m'")) \in "Fors")) /\ eventually (on "n'", event[]<- CPLDeliver $ "n" $ "m'"))))}).
  d_head.
  rewrite_assertion_pos.
  d_swap; d_clear.
  d_swap; d_clear.

  d_have {A:
            on "n", event[]-> CPLSend $ "n'" $ "m" =>>
                                      ((self-event /\ "Fn" = "n" /\ CPair $ 0 $ (CSLSend $ "n'" $ (CPair $ "c" $ "m")) \in "Fors") /\ eventually (on "n'", event[]<- CPLDeliver $ "n" $ "m"))
                              \/
                              ((self-event /\ "Fn" = "n" /\ CPair $ 0 $ (CSLSend $ "n'" $ (CPair $ "c" $ "m")) \in "Fors") /\ (eventually^ ((self-event /\ "Fn" = "n" /\ CPair $ 0 $ (CSLSend $ "n'" $ (CPair $ "c" $ "m'")) \in "Fors") /\ eventually (on "n'", event[]<- CPLDeliver $ "n" $ "m'"))))
                              \/
                              ((self-event /\ "Fn" = "n" /\ CPair $ 0 $ (CSLSend $ "n'" $ (CPair $ "c" $ "m")) \in "Fors") /\ ((self-event /\ "Fn" = "n" /\ CPair $ 0 $ (CSLSend $ "n'" $ (CPair $ "c" $ "m")) \in "Fors") /\ eventually (on "n'", event[]<- CPLDeliver $ "n" $ "m")))
                              \/
                              ((self-event /\ "Fn" = "n" /\ CPair $ 0 $ (CSLSend $ "n'" $ (CPair $ "c" $ "m")) \in "Fors") /\ (eventuallyp^ ((self-event /\ "Fn" = "n" /\ CPair $ 0 $ (CSLSend $ "n'" $ (CPair $ "c" $ "m'")) \in "Fors") /\ eventually (on "n'", event[]<- CPLDeliver $ "n" $ "m'"))))
         }.
  {

    set D1 := {A:  eventually ((on "n'", event[]<- CPLDeliver $ "n" $ "m"))}.
    set D2 := {A:  eventually ((on "n'", event[]<- CPLDeliver $ "n" $ "m'"))}.

    set A1 := {A: (self-event /\ "Fn" = "n" /\ CPair $ 0 $ (CSLSend $ "n'" $ (CPair $ "c" $ "m")) \in "Fors")}.
    set A2 := {A: (self-event /\ "Fn" = "n" /\ CPair $ 0 $ (CSLSend $ "n'" $ (CPair $ "c" $ "m'")) \in "Fors")}.
    set E1 := {A: (eventually^ ((self-event /\ "Fn" = "n" /\ ((0, CSLSend $ "n'" $ ("c", "m")) \in "Fors")) /\ eventually (on "n'", event[]<- CPLDeliver $ "n" $ "m")))}.
    set E2 := {A: (eventually^ ((self-event /\ "Fn" = "n" /\ ((0, CSLSend $ "n'" $ ("c", "m'")) \in "Fors")) /\ eventually (on "n'", event[]<- CPLDeliver $ "n" $ "m'")))}.

    set F1 := {A: (eventuallyp^ ((self-event /\ "Fn" = "n" /\ ((0, CSLSend $ "n'" $ ("c", "m")) \in "Fors")) /\ eventually (on "n'", event[]<- CPLDeliver $ "n" $ "m")))}.
    set F2 := {A: (eventuallyp^ ((self-event /\ "Fn" = "n" /\ ((0, CSLSend $ "n'" $ ("c", "m'")) \in "Fors")) /\ eventually (on "n'", event[]<- CPLDeliver $ "n" $ "m'")))}.

    set G1 := {A: ((self-event /\ "Fn" = "n" /\ ((0, CSLSend $ "n'" $ ("c", "m")) \in "Fors")) /\ eventually (on "n'", event[]<- CPLDeliver $ "n" $ "m"))}.
    set G2 := {A: ((self-event /\ "Fn" = "n" /\ ((0, CSLSend $ "n'" $ ("c", "m'")) \in "Fors")) /\ eventually (on "n'", event[]<- CPLDeliver $ "n" $ "m'"))}.

    eapply DARewriteIffPL with (Arp := {A: A1 /\ (D1 \/ E2 \/ G1 \/ F2)})
                               (Arc := {A: (A1 /\ D1) \/ (A1 /\ E2) \/ (A1 /\ G1) \/ (A1 /\ F2)}).

    eapply DSOrDistributesAnd4.
    rewrite_assertion_any.
    d_head.
  }

  d_have {A:
             ((self-event /\ "Fn" = "n" /\ CPair $ 0 $ (CSLSend $ "n'" $ (CPair $ "c" $ "m")) \in "Fors") /\ (eventually^ ((self-event /\ "Fn" = "n" /\ CPair $ 0 $ (CSLSend $ "n'" $ (CPair $ "c" $ "m'")) \in "Fors") /\ eventually (on "n'", event[]<- CPLDeliver $ "n" $ "m'"))))
                              \/
                              ((self-event /\ "Fn" = "n" /\ CPair $ 0 $ (CSLSend $ "n'" $ (CPair $ "c" $ "m")) \in "Fors") /\ ((self-event /\ "Fn" = "n" /\ CPair $ 0 $ (CSLSend $ "n'" $ (CPair $ "c" $ "m")) \in "Fors") /\ eventually (on "n'", event[]<- CPLDeliver $ "n" $ "m")))
                              \/
                              ((self-event /\ "Fn" = "n" /\ CPair $ 0 $ (CSLSend $ "n'" $ (CPair $ "c" $ "m")) \in "Fors") /\ (eventuallyp^ ((self-event /\ "Fn" = "n" /\ CPair $ 0 $ (CSLSend $ "n'" $ (CPair $ "c" $ "m'")) \in "Fors") /\ eventually (on "n'", event[]<- CPLDeliver $ "n" $ "m'"))))
             ->
            ((self-event /\ "Fn" = "n" /\ CPair $ 0 $ (CSLSend $ "n'" $ (CPair $ "c" $ "m")) \in "Fors") /\ (eventually^ ((self-event /\ "Fn" = "n" /\ CPair $ 0 $ (CSLSend $ "n'" $ (CPair $ "c" $ "m'")) \in "Fors"))))
            \/
            ((self-event /\ "Fn" = "n" /\ CPair $ 0 $ (CSLSend $ "n'" $ (CPair $ "c" $ "m")) \in "Fors") /\ eventually (on "n'", event[]<- CPLDeliver $ "n" $ "m"))
            \/
            ((self-event /\ "Fn" = "n" /\ CPair $ 0 $ (CSLSend $ "n'" $ (CPair $ "c" $ "m")) \in "Fors") /\ (eventuallyp^ ((self-event /\ "Fn" = "n" /\ CPair $ 0 $ (CSLSend $ "n'" $ (CPair $ "c" $ "m'")) \in "Fors"))))
         }.
  {
    set A1 := {A: (self-event /\ "Fn" = "n" /\ CPair $ 0 $ (CSLSend $ "n'" $ (CPair $ "c" $ "m")) \in "Fors")}.

    set B1 := {A: eventually on "n'", event []<- CPLDeliver $ "n" $ "m"}.

    d_have {A:
              eventually^ ((self-event /\ "Fn" = "n" /\ CPair $ 0 $ (CSLSend $ "n'" $ (CPair $ "c" $ "m'")) \in "Fors") /\ eventually (on "n'", event[]<- CPLDeliver $ "n" $ "m'"))
              ->
              eventually^ ((self-event /\ "Fn" = "n" /\ CPair $ 0 $ (CSLSend $ "n'" $ (CPair $ "c" $ "m'")) \in "Fors"))
           }.
    {
      d_have {A:
              ((self-event /\ "Fn" = "n" /\ CPair $ 0 $ (CSLSend $ "n'" $ (CPair $ "c" $ "m'")) \in "Fors") /\ eventually (on "n'", event[]<- CPLDeliver $ "n" $ "m'"))
              ->
              (self-event /\ "Fn" = "n" /\ CPair $ 0 $ (CSLSend $ "n'" $ (CPair $ "c" $ "m'")) \in "Fors")
             }.
      {
        d_ifc. d_splitp. d_head.
      }
      d_ifc.
      eapply DARewriteIfP with (Arp := {A: ((self-event /\ "Fn" = "n" /\ CPair $ 0 $ (CSLSend $ "n'" $ (CPair $ "c" $ "m'")) \in "Fors") /\ eventually (on "n'", event[]<- CPLDeliver $ "n" $ "m'"))})
                               (Arc := {A: ((self-event /\ "Fn" = "n" /\ CPair $ 0 $ (CSLSend $ "n'" $ (CPair $ "c" $ "m'")) \in "Fors"))}).
      d_head. rewrite_assertion_pos.
      d_head.
    }

    d_have {A:
              eventuallyp^ ((self-event /\ "Fn" = "n" /\ CPair $ 0 $ (CSLSend $ "n'" $ (CPair $ "c" $ "m'")) \in "Fors") /\ eventually (on "n'", event[]<- CPLDeliver $ "n" $ "m'"))
              ->
              eventuallyp^ ((self-event /\ "Fn" = "n" /\ CPair $ 0 $ (CSLSend $ "n'" $ (CPair $ "c" $ "m'")) \in "Fors"))
           }.
    {
      d_have {A:
              ((self-event /\ "Fn" = "n" /\ CPair $ 0 $ (CSLSend $ "n'" $ (CPair $ "c" $ "m'")) \in "Fors") /\ eventually (on "n'", event[]<- CPLDeliver $ "n" $ "m'"))
              ->
              (self-event /\ "Fn" = "n" /\ CPair $ 0 $ (CSLSend $ "n'" $ (CPair $ "c" $ "m'")) \in "Fors")
             }.
      {
        d_ifc. d_splitp. d_head.
      }
      d_ifc.
      eapply DARewriteIfP with (Arp := {A: ((self-event /\ "Fn" = "n" /\ CPair $ 0 $ (CSLSend $ "n'" $ (CPair $ "c" $ "m'")) \in "Fors") /\ eventually (on "n'", event[]<- CPLDeliver $ "n" $ "m'"))})
                               (Arc := {A: ((self-event /\ "Fn" = "n" /\ CPair $ 0 $ (CSLSend $ "n'" $ (CPair $ "c" $ "m'")) \in "Fors"))}).
      d_head. rewrite_assertion_pos.
      d_head.
    }

    d_ifc.

    eapply DARewriteIfP with (Arp := {A:
                                        eventuallyp^ ((self-event /\ "Fn" = "n" /\ CPair $ 0 $ (CSLSend $ "n'" $ (CPair $ "c" $ "m'")) \in "Fors") /\
                                                      eventually on "n'", event []<- CPLDeliver $ "n" $ "m'")})
                             (Arc := {A:
                                        eventuallyp^ (self-event /\ "Fn" = "n" /\ CPair $ 0 $ (CSLSend $ "n'" $ (CPair $ "c" $ "m'")) \in "Fors")}).
    d_head. rewrite_assertion_pos.

    set A2 := {A: (self-event /\ "Fn" = "n" /\ CPair $ 0 $ (CSLSend $ "n'" $ (CPair $ "c" $ "m'")) \in "Fors")}.
    set B2 := {A: eventually on "n'", event []<- CPLDeliver $ "n" $ "m'"}.

     eapply DARewriteIfP with (Arp := {A:
                                        eventually^ ((self-event /\ "Fn" = "n" /\ CPair $ 0 $ (CSLSend $ "n'" $ (CPair $ "c" $ "m'")) \in "Fors") /\
                                                      eventually on "n'", event []<- CPLDeliver $ "n" $ "m'")})
                             (Arc := {A:
                                        eventually^ (self-event /\ "Fn" = "n" /\ CPair $ 0 $ (CSLSend $ "n'" $ (CPair $ "c" $ "m'")) \in "Fors")}).
     d_swap. d_head. rewrite_assertion_pos.
     set A3 := {A: (self-event /\ "Fn" = "n" /\ CPair $ 0 $ (CSLSend $ "n'" $ (CPair $ "c" $ "m")) \in "Fors")}.
     set B3 := {A: eventually on "n'", event []<- CPLDeliver $ "n" $ "m"}.

     d_have {A:
               A3 /\ A3 /\ B3 -> A3 /\ B3}.
     {
       d_ifc. d_splitp. d_splitc. d_head. d_clear. d_splitp. d_clear. d_head.
     }
     d_swap. eapply DARewriteIfP with (Arp := {A: A3 /\ A3 /\ B3})
                                      (Arc := {A: A3 /\ B3}).
     d_head. rewrite_assertion_pos.

     d_head.
  }

  d_have {A:
            on "n", event[]-> CPLSend $ "n'" $ "m" =>>
                                      ((self-event /\ "Fn" = "n" /\ CPair $ 0 $ (CSLSend $ "n'" $ (CPair $ "c" $ "m")) \in "Fors") /\ eventually (on "n'", event[]<- CPLDeliver $ "n" $ "m"))
                              \/
                              ((self-event /\ "Fn" = "n" /\ CPair $ 0 $ (CSLSend $ "n'" $ (CPair $ "c" $ "m")) \in "Fors") /\ (eventually^ ((self-event /\ "Fn" = "n" /\ CPair $ 0 $ (CSLSend $ "n'" $ (CPair $ "c" $ "m'")) \in "Fors"))))
                              \/
                              ((self-event /\ "Fn" = "n" /\ CPair $ 0 $ (CSLSend $ "n'" $ (CPair $ "c" $ "m")) \in "Fors") /\ eventually (on "n'", event[]<- CPLDeliver $ "n" $ "m"))
                              \/
                              ((self-event /\ "Fn" = "n" /\ CPair $ 0 $ (CSLSend $ "n'" $ (CPair $ "c" $ "m")) \in "Fors") /\ (eventuallyp^ ((self-event /\ "Fn" = "n" /\ CPair $ 0 $ (CSLSend $ "n'" $ (CPair $ "c" $ "m'")) \in "Fors"))))
         }.
  {
    d_swap.
    eapply DARewriteIfP with (Arp := {A: (self-event /\ "Fn" = "n" /\ CPair $ 0 $ (CSLSend $ "n'" $ (CPair $ "c" $ "m")) \in "Fors") /\
                        eventually^ ((self-event /\ "Fn" = "n" /\ CPair $ 0 $ (CSLSend $ "n'" $ (CPair $ "c" $ "m'")) \in "Fors") /\
                                     eventually on "n'", event []<- CPLDeliver $ "n" $ "m'") \/
                        (self-event /\ "Fn" = "n" /\ CPair $ 0 $ (CSLSend $ "n'" $ (CPair $ "c" $ "m")) \in "Fors") /\
                        (self-event /\ "Fn" = "n" /\ CPair $ 0 $ (CSLSend $ "n'" $ (CPair $ "c" $ "m")) \in "Fors") /\ eventually on "n'", event []<- CPLDeliver $ "n" $ "m" \/
                        (self-event /\ "Fn" = "n" /\ CPair $ 0 $ (CSLSend $ "n'" $ (CPair $ "c" $ "m")) \in "Fors") /\
                        eventuallyp^ ((self-event /\ "Fn" = "n" /\ CPair $ 0 $ (CSLSend $ "n'" $ (CPair $ "c" $ "m'")) \in "Fors") /\
                                      eventually on "n'", event []<- CPLDeliver $ "n" $ "m'")})
                             (Arc := {A: (self-event /\ "Fn" = "n" /\ CPair $ 0 $ (CSLSend $ "n'" $ (CPair $ "c" $ "m")) \in "Fors") /\
                        eventually^ (self-event /\ "Fn" = "n" /\ CPair $ 0 $ (CSLSend $ "n'" $ (CPair $ "c" $ "m'")) \in "Fors") \/
                        (self-event /\ "Fn" = "n" /\ CPair $ 0 $ (CSLSend $ "n'" $ (CPair $ "c" $ "m")) \in "Fors") /\ eventually on "n'", event []<- CPLDeliver $ "n" $ "m" \/
                        (self-event /\ "Fn" = "n" /\ CPair $ 0 $ (CSLSend $ "n'" $ (CPair $ "c" $ "m")) \in "Fors") /\
                        eventuallyp^ (self-event /\ "Fn" = "n" /\ CPair $ 0 $ (CSLSend $ "n'" $ (CPair $ "c" $ "m'")) \in "Fors")}).
    d_head. rewrite_assertion_pos.
    d_head.
  }

  d_have {A:
            on "n", event[]-> CPLSend $ "n'" $ "m" =>>
                                      ((self-event /\ "Fn" = "n" /\ CPair $ 0 $ (CSLSend $ "n'" $ (CPair $ "c" $ "m")) \in "Fors") /\ eventually (on "n'", event[]<- CPLDeliver $ "n" $ "m"))
                              \/
                              AFalse
                              \/
                              ((self-event /\ "Fn" = "n" /\ CPair $ 0 $ (CSLSend $ "n'" $ (CPair $ "c" $ "m")) \in "Fors") /\ eventually on "n'", event []<- CPLDeliver $ "n" $ "m")
                              \/
                              AFalse
         }.
  {
    d_have {A:
              self-event /\ on "n", ((0, CSLSend $ "n'" $ ("c", "m")) \in "Fors") =>>
                                                                                  always^ ~(self-event /\
                                                                                            on "n", ((0, CSLSend $ "n'" $ ("c", "m'")) \in "Fors"))
           }.
    {
      do 12 d_clear.
      eapply L37_1.
    }

    d_have {A:
              (self-event /\ "Fn" = "n" /\ CPair $ 0 $ (CSLSend $ "n'" $ (CPair $ "c" $ "m")) \in "Fors") /\
              eventually^ (self-event /\ "Fn" = "n" /\ CPair $ 0 $ (CSLSend $ "n'" $ (CPair $ "c" $ "m'")) \in "Fors")
              -> AFalse
           }.
    {
      d_ifc. d_splitp.
      eapply DARewriteEntailsP with (Arp := {A: self-event /\ on "n", (CPair $ 0 $ (CSLSend $ "n'" $ (CPair $ "c" $ "m")) \in "Fors")})
                                    (Arc := {A:  always^ (~ (self-event /\ on "n", (CPair $ 0 $ (CSLSend $ "n'" $ (CPair $ "c" $ "m'")) \in "Fors")))}).
      d_swap. d_head. rewrite_assertion_pos.

      d_have {A:
                ~ eventually^ (self-event /\ "Fn" = "n" /\ CPair $ 0 $ (CSLSend $ "n'" $ (CPair $ "c" $ "m'")) \in "Fors")
             }.
      {
        eapply DARewriteCongruentPR with (Arc := {A:
                                                    always^ (~ (self-event /\ on "n", (CPair $ 0 $ (CSLSend $ "n'" $ (CPair $ "c" $ "m'")) \in "Fors")))})
                                         (Arp := {A:
                                                    ~ eventually^ (self-event /\ "Fn" = "n" /\ CPair $ 0 $ (CSLSend $ "n'" $ (CPair $ "c" $ "m'")) \in "Fors")}).

        eapply DTL114_1.
        rewrite_assertion_any.
        d_head.
      }
      set F := {A:  eventually^ (self-event /\ "Fn" = "n" /\ CPair $ 0 $ (CSLSend $ "n'" $ (CPair $ "c" $ "m'")) \in "Fors")}.
      eapply DSCut; first by eapply DSNotImpliesFalse with (Ac := {A: F}).
      d_splitp. d_swap; d_clear.
      d_swap.
      eapply DARewriteIfP with (Arp := {A: ~ F})
                               (Arc := {A: F -> AFalse}).
      d_head. rewrite_assertion_pos. d_swap. d_rotate 3.
      eapply DARewriteIfP with (Arp := {A: F})
                               (Arc := {A: AFalse}).
      d_rotate 16. d_head. rewrite_assertion_pos.
      d_false.
    }

    d_have {A:
              self-event /\ on "n", ((0, CSLSend $ "n'" $ ("c", "m")) \in "Fors") =>>
                                                                                  alwaysp^ ~(self-event /\
                                                                                            on "n", ((0, CSLSend $ "n'" $ ("c", "m'")) \in "Fors"))
           }.
    {
      do 14 d_clear.
      eapply L37_2.
    }
    d_have {A:
              (self-event /\ "Fn" = "n" /\ CPair $ 0 $ (CSLSend $ "n'" $ (CPair $ "c" $ "m")) \in "Fors") /\
              eventuallyp^ (self-event /\ "Fn" = "n" /\ CPair $ 0 $ (CSLSend $ "n'" $ (CPair $ "c" $ "m'")) \in "Fors")
              -> AFalse
           }.
    {
      d_ifc. d_splitp.
      eapply DARewriteEntailsP with (Arp := {A: self-event /\ on "n", (CPair $ 0 $ (CSLSend $ "n'" $ (CPair $ "c" $ "m")) \in "Fors")})
                                    (Arc := {A:  alwaysp^ (~ (self-event /\ on "n", (CPair $ 0 $ (CSLSend $ "n'" $ (CPair $ "c" $ "m'")) \in "Fors")))}).
      d_swap. d_head. rewrite_assertion_pos.

      d_have {A:
                ~ eventuallyp^ (self-event /\ "Fn" = "n" /\ CPair $ 0 $ (CSLSend $ "n'" $ (CPair $ "c" $ "m'")) \in "Fors")
             }.
      {
        eapply DARewriteCongruentPR with (Arc := {A:
                                                    alwaysp^ (~ (self-event /\ on "n", (CPair $ 0 $ (CSLSend $ "n'" $ (CPair $ "c" $ "m'")) \in "Fors")))})
                                         (Arp := {A:
                                                    ~ eventuallyp^ (self-event /\ "Fn" = "n" /\ CPair $ 0 $ (CSLSend $ "n'" $ (CPair $ "c" $ "m'")) \in "Fors")}).

        eapply DTL114.
        rewrite_assertion_any.

        d_head.
      }
      set F := {A:  eventuallyp^ (self-event /\ "Fn" = "n" /\ CPair $ 0 $ (CSLSend $ "n'" $ (CPair $ "c" $ "m'")) \in "Fors")}.
      eapply DSCut; first by eapply DSNotImpliesFalse with (Ac := {A: F}).
      d_splitp. d_swap; d_clear.
      d_swap.
      eapply DARewriteIfP with (Arp := {A: ~ F})
                               (Arc := {A: F -> AFalse}).
      d_head. rewrite_assertion_pos. d_swap. d_rotate 3.
      eapply DARewriteIfP with (Arp := {A: F})
                               (Arc := {A: AFalse}).
      d_rotate 18. d_head. rewrite_assertion_pos.
      d_false.
  }

    d_swap; d_clear.
    d_rotate 4. d_swap.
    do 11 d_clear. d_rotate 5.
    eapply DARewriteIfP with (Arp := {A: ((self-event /\ "Fn" = "n" /\ CPair $ 0 $ (CSLSend $ "n'" $ (CPair $ "c" $ "m")) \in "Fors") /\
                                          eventuallyp^ (self-event /\ "Fn" = "n" /\ CPair $ 0 $ (CSLSend $ "n'" $ (CPair $ "c" $ "m'")) \in "Fors"))})
                             (Arc := {A: AFalse}).
    d_rotate 2. d_head.
    rewrite_assertion_pos.
    eapply DARewriteIfP with (Arp := {A: ((self-event /\ "Fn" = "n" /\ CPair $ 0 $ (CSLSend $ "n'" $ (CPair $ "c" $ "m")) \in "Fors") /\
                                          eventually^ (self-event /\ "Fn" = "n" /\ CPair $ 0 $ (CSLSend $ "n'" $ (CPair $ "c" $ "m'")) \in "Fors"))})
                             (Arc := {A: AFalse}).
    d_rotate 3. d_head.
    rewrite_assertion_pos.
    d_head.
  }
  do 10 (d_swap; d_clear).

  d_have {A:
            (self-event /\ "Fn" = "n" /\ CPair $ 0 $ (CSLSend $ "n'" $ (CPair $ "c" $ "m")) \in "Fors") /\ eventually on "n'", event []<- CPLDeliver $ "n" $ "m" \/
                        AFalse \/
                        (self-event /\ "Fn" = "n" /\ CPair $ 0 $ (CSLSend $ "n'" $ (CPair $ "c" $ "m")) \in "Fors") /\ eventually on "n'", event []<- CPLDeliver $ "n" $ "m" \/
                                                                                                                                           AFalse
                                                                                                                                           ->
                                                                                                                                           (self-event /\ "Fn" = "n" /\ CPair $ 0 $ (CSLSend $ "n'" $ (CPair $ "c" $ "m")) \in "Fors") /\ eventually on "n'", event []<- CPLDeliver $ "n" $ "m" \/
                                                                                                                                                                                                                                                              (self-event /\ "Fn" = "n" /\ CPair $ 0 $ (CSLSend $ "n'" $ (CPair $ "c" $ "m")) \in "Fors") /\ eventually on "n'", event []<- CPLDeliver $ "n" $ "m"}.
  {
    d_ifc.
    d_orp. d_left. d_head.
    d_orp. d_false.
    d_orp. d_left. d_head.
    d_false.
  }

  d_swap. eapply DARewriteIfP; first by d_head. rewrite_assertion_pos.
  d_swap; d_clear.

  d_have {A:
           (self-event /\ "Fn" = "n" /\ CPair $ 0 $ (CSLSend $ "n'" $ (CPair $ "c" $ "m")) \in "Fors") /\ eventually on "n'", event []<- CPLDeliver $ "n" $ "m"
                                                                                                                              ->
                                                                                                                              eventually on "n'", event []<- CPLDeliver $ "n" $ "m"
         }.
  {
    d_ifc. d_splitp. d_swap. d_head.
  }
  d_swap.
  set X := {A: (self-event /\ "Fn" = "n" /\ CPair $ 0 $ (CSLSend $ "n'" $ (CPair $ "c" $ "m")) \in "Fors") /\ eventually on "n'", event []<- CPLDeliver $ "n" $ "m"}.

  d_have {A:
            X \/ X -> X}.
  {
    d_ifc. d_orp. d_head. d_head.
  }

  d_swap. eapply DARewriteIfP; first by d_head. rewrite_assertion_pos.
  d_swap; d_clear.
  eapply DARewriteIfP; first by d_head. rewrite_assertion_pos.
  d_head.
Qed.

(* Lemmas used in proving PL_2 *)
Lemma L43 :
  Context
    [:: V "c"; V "m"; V "n'"; V "n"]
    [::] |- perfect_link, {A:
    self (
      ("n'", "c") \in (FRight $ ("Fs" $ "n")) /\
      eventuallyp on "n", event [0]<- CSLDeliver $ "n'" $ ("c", "m") =>>
      "Fn" = "n" -> (CPLDeliver $ "n'" $ "m") \notin "Fois"
    )
  }.
Proof.

  d_have {A:
            self (
      ("n'", "c") \in (FRight $ ("Fs" $ "n")) /\
      eventuallyp on "n", event [0]<- CSLDeliver $ "n'" $ ("c", "m") =>>
      "Fn" = "n" -> (CPLDeliver $ "n'" $ "m") \notin "Fois"
              )
         }.
  {
    set A := {A: CPair $ "n'" $ "c" \in FRight $ ("Fs" $ "n") /\ eventuallyp on "n", event [0]<- CSLDeliver $ "n'" $ ("c", "m") -> "Fn" = "n" -> CPLDeliver $ "n'" $ "m" \notin "Fois"}.
    eapply DSCut; first by apply DPInvSe with (A := A).

    d_ifp.
    (* for request, by IR *)
    d_have {A:
              (forall: "e" : event []-> "e" =>> A) -> self (forall: "e" : event []-> "e" =>> A)
           }.
    {
      eapply DTL129.
    }
    eapply DARewriteIfC; first by d_head.
    rewrite_assertion_pos. d_clear.
    d_use DPIR.
    d_forallp {t: "e"}. d_evalp.
    d_have {A:
               CPair $ (CPair $ ("Fs'" $ "Fn") $ "Fors") $ "Fois" =
                        match: "Fs" $ "Fn"
                        with: {{(#, #) ->
                                match: "e"
                                with: {{CPLSend $ # $ # ->
                                        match: FSucc $ (P 1 0)
                                        with: {{# ->
                                                match: CPair $ 0 $ (CSLSend $ (P 1 0) $ (CPair $ (P 0 0) $ (P 1 1)))
                                                with: {{# -> CPair $ (CPair $ (CPair $ (P 1 0) $ (P 3 1)) $ (CCons $ (P 0 0) $ CNil)) $ CNil}}}}}}}}
                                -> A
           }.
    {
      d_ifc.
      d_destructp (fun t => {A: ("Fs'" $ "Fn", "Fors", "Fois") = t}).
      d_forallp "r"; d_forallp "c".
      d_splitp. d_swap. d_substp. d_evalp.
      d_destructp (fun t => {A: ("Fs'" $ "Fn", "Fors", "Fois") = t}).
      d_forallp "m"; d_forallp "n'".
      d_splitp. d_swap. d_substp. d_evalp.
      d_destructtuplep
        {t: "Fs'" $ "Fn"} {t: "Fors"} {t: "Fois"}
        {t: (FSucc $ "c", "r")}
        {t: (CCons $ (CPair $ 0 $ (CSLSend $ "n'" $ (CPair $ (FSucc $ "c") $ "m"))) $ CNil)} {t: CNil}; do 2 d_splitp.
      d_subst.
      d_ifc. d_ifc.
      d_notc.
      eapply DSCut; first by eapply DAPInNil.
      d_forallp {t: (CPLDeliver $ "n'" $ "m")}.
      eapply DSCut; first by eapply DSNotImpliesFalse with (Ac := {A: (CPLDeliver $ "n'" $ "m") \in CNil}).
      d_swap; eapply DARewriteIffPL; first by d_head.
      rewrite_assertion_any; d_swap; d_clear.
      d_ifp. d_head. d_false.
    }
    d_swap. eapply DARewriteIfP; first by d_head.
    rewrite_assertion_pos.
    d_forallc "e". d_head.

    (* for indication, *)
    d_ifp.
    d_have {A:
              (forall: "i", "e" : event ["i"]<- "e" =>> A) -> self (forall: "i", "e" : event ["i"]<- "e" =>> A)
           }.
    eapply DTL129.
    eapply DARewriteIfC; first by d_head.
    rewrite_assertion_pos. d_clear.
    d_use DPII.
    d_forallp "i". d_forallp "e". d_evalp.
    d_have {A:
              CPair $ (CPair $ ("Fs'" $ "Fn") $ "Fors") $ "Fois" =
                        match: "Fs" $ "Fn"
                        with: {{(#, #) ->
                                match: CPair $ "i" $ "e"
                                with: {{(0, CSLDeliver $ # $ (#, #)) ->
                                        match: (fun: fun: (fun: fun: FNot $ (FEqual $ (P 1 0) $ (P 0 0))) $ (FCount $ (P 1 0) $ (P 0 0)) $ 0) $ (CPair $ (P 0 0) $ (P 0 1)) $
                                               (P 1 1)
                                        with: {{true -> CPair $ (CPair $ ("Fs" $ "Fn") $ CNil) $ CNil| false -> match: FUnion $ (P 2 1) $ (CCons $ (CPair $ (P 1 0) $ (P 1 1)) $ CNil) with: {{# -> match: CPLDeliver $ (P 2 0) $ (P 2 2) with: {{# -> CPair $ (CPair $ (CPair $ (P 4 0) $ (FUnion $ (P 4 1) $ (CCons $ (CPair $ (P 3 0) $ (P 3 1)) $ CNil))) $ CNil) $ (CCons $ (CPLDeliver $ (P 3 0) $ (P 3 2)) $ CNil)}}}}}}}}}}
                              -> A}.
    {
      d_ifc.
      d_destructp (fun t => {A: ("Fs'" $ "Fn", "Fors", "Fois") = t}).
      d_forallp "r"; d_forallp "c'".
      d_splitp. d_swap. d_substp. d_evalp.
      d_destructp (fun t => {A: ("Fs'" $ "Fn", "Fors", "Fois") = t}).
      d_forallp "m"; d_forallp "c". d_forallp "n".
      d_splitp. d_swap. d_substp. d_evalp.
      d_destructp (fun t => {A: ("Fs'" $ "Fn", "Fors", "Fois") = t}).
      d_orp.
      d_splitp. d_swap. d_substp. d_evalp.
      d_destructtuplep
        {t: "Fs'" $ "Fn"} {t: "Fors"} {t: "Fois"}
        {t: (CPair $ "c'" $ "r")}
        {t: CNil} {t: CNil}; do 2 d_splitp.
      d_ifc. d_ifc. d_notc.
      d_substp.
      eapply DSCut; first by eapply DAPInNil.
      d_forallp {t: (CPLDeliver $ "n'" $ "m")}.
      eapply DSCut; first by eapply DSNotImpliesFalse with (Ac := {A: (CPLDeliver $ "n'" $ "m") \in CNil}).
      d_swap; eapply DARewriteIffPL; first by d_head.
      rewrite_assertion_any; d_swap; d_clear.
      d_ifp. d_head. d_false.

      d_splitp. d_swap. d_substp. d_evalp.
      d_destructtuplep
        {t: "Fs'" $ "Fn"} {t: "Fors"} {t: "Fois"}
        {t: (CPair $ "c'" $ (FUnion $ "r" $ (CCons $ (CPair $ "n" $ "c") $ CNil)))}
        {t: CNil} {t: (CCons $ (CPLDeliver $ "n" $ "m") $ CNil)}; do 2 d_splitp.
      d_ifc. d_ifc. d_notc.
      d_substp.
      eapply DSCut; first by eapply DAPNotInCons.
      d_forallp {t: CPLDeliver $ "n'" $ "m"}.
      d_forallp {t: (CPLDeliver $ "n" $ "m")}.
      d_forallp {t: CNil}.
      d_splitp. d_clear.
      d_ifp. d_splitc.
      d_notc.
      eapply DSEqualEvent.
      d_splitp. d_rotate 11. d_clear.
      d_rotate 4. d_splitp. d_rotate 5.
      eapply DSCut; first by apply DAPInEliminateFalse.
      d_forallp {t: CPair $ "n'" $ "c"}. d_forallp "r".
      d_evalp. d_splitp. d_swap; d_clear. d_substp. d_ifp. d_head.
      d_use DAPEqualSymmetric. d_forallp "n". d_forallp "Fn".
      d_splitp. d_clear. d_ifp. d_rotate 7. d_head.
      d_rotate 9. d_subst. d_substp. d_evalp.
      d_rotate 6. d_notp. d_rotate 7. d_substp. d_head.

      d_notc.
      eapply DSCut; first by eapply DAPInNil.
      d_forallp {t: (CPLDeliver $ "n'" $ "m")}.
      eapply DSCut; first by eapply DSNotImpliesFalse with (Ac := {A: (CPLDeliver $ "n'" $ "m") \in CNil}).
      d_swap; eapply DARewriteIffPL; first by d_head.
      rewrite_assertion_any; d_swap; d_clear.
      d_ifp. d_head. d_false.
      d_notp. d_head.
    }
    d_swap. eapply DARewriteIfP; first by d_head.
    rewrite_assertion_pos.
    d_forallc "i". d_forallc "e".
    d_head.

    (* for peridoic, by Pe *)
    d_ifp.
    d_have {A:
              (event []~> periodic_event.PE =>> A) -> self (event []~> periodic_event.PE =>> A)
           }.
    eapply DTL129.
    eapply DARewriteIfC; first by d_head.
    rewrite_assertion_pos. d_clear.
    d_use DPPe.
    d_have {A:
              CPair $ (CPair $ ("Fs'" $ "Fn") $ "Fors") $ "Fois" = periodic perfect_link $ "Fn" $ ("Fs" $ "Fn") -> A}.
    {
      d_ifc. d_eval.
      d_destructtuplep
        {t: "Fs'" $ "Fn"} {t: "Fors"} {t: "Fois"}
        {t: ("Fs" $ "Fn")}
        {t: CNil} {t: CNil}; do 2 d_splitp.
      d_ifc. d_ifc. d_notc.
      d_substp.
      eapply DSCut; first by eapply DAPInNil.
      d_forallp {t: (CPLDeliver $ "n'" $ "m")}.
      eapply DSCut; first by eapply DSNotImpliesFalse with (Ac := {A: (CPLDeliver $ "n'" $ "m") \in CNil}).
      d_swap; eapply DARewriteIffPL; first by d_head.
      rewrite_assertion_any; d_swap; d_clear.
      d_ifp. d_head. d_false.
    }
    d_swap. eapply DARewriteIfP; first by d_head.
    rewrite_assertion_pos. d_head.
    d_head.
  }
  d_head.
Qed.

Lemma L42 :
  Context
    [:: V "c"; V "m"; V "n'"; V "n"]
    [::] |- perfect_link, {A:
    self (
      "Fn" = "n" /\ (CPLDeliver $ "n'" $ "m") \in "Fois" =>>
      always^ ("Fn" = "n" -> (CPLDeliver $ "n'" $ "m") \notin "Fois") /\
      alwaysp^ ("Fn" = "n" -> (CPLDeliver $ "n'" $ "m") \notin "Fois")
    )
  }.
Proof.
  (* by InvLSE *)
  d_have {A:
            self (
                "Fn" = "n" /\ (CPLDeliver $ "n'" $ "m" \in "Fois") =>>
                                                                     (("n'", "c") \in (FRight $ ("Fs'" $ "n"))) /\ (on "n", event[0]<- CSLDeliver $ "n'" $ ("c", "m"))
              )
         }.
  {
    eapply DSCut; first by apply DPInvLSE with (A := {A:
          ("Fn" = "n" /\ (CPLDeliver $ "n'" $ "m" \in "Fois")) ->
          (("n'", "c") \in (FRight $ ("Fs'" $ "n"))) /\ (on "n", event[0]<- CSLDeliver $ "n'" $ ("c", "m"))});
    first by repeat constructor.

    (* request *)
    d_ifp. d_forallc "e".
    d_ifc. d_splitp. d_swap. d_eval.
    d_destructp (fun t => {A: ("Fs'" $ "Fn", "Fors", "Fois") = t}).
    d_forallp {t: CNil}. d_forallp "c". d_splitp. d_swap.
    d_substp. d_eval.
    d_destructp (fun t => {A: ("Fs'" $ "Fn", "Fors", "Fois") = t}).
    d_forallp {t: ("c", "m")}. d_forallp "n'".
    d_splitp. d_swap. d_substp. d_eval.
    d_ifc. d_swap.
    d_destructtuplep
      {t: "Fs'" $ "Fn"} {t: "Fors"} {t: "Fois"}
      {t: (CPair $ (FSucc $ "c") $ CNil)}
      {t: (CCons $ (CPair $ 0 $ (CSLSend $ "n'" $ (CPair $ (FSucc $ "c") $ (CPair $ "c" $ "m")))) $ CNil)} {t: CNil}; do 2 d_splitp.
    d_rotate 3. d_substp. d_splitp. d_swap.
    eapply DSCut; first by eapply DAPInNil.
    d_forallp {t: (CPLDeliver $ "n'" $ "m")}.
    eapply DSCut; first by eapply DSNotImpliesFalse with (Ac := {A: (CPLDeliver $ "n'" $ "m") \in CNil}).
    d_swap; eapply DARewriteIffPL; first by d_head.
    rewrite_assertion_any; d_swap; d_clear.
    d_ifp. d_head. d_false.

    (* indication *)
    d_ifp. d_forallc "i". d_forallc "e".
    d_ifc. d_splitp. d_swap. d_eval.
    d_destructp (fun t => {A: ("Fs'" $ "Fn", "Fors", "Fois") = t}).
    d_forallp {t: CNil}; d_forallp "c"; d_splitp; d_swap.
    d_substp; d_evalp.
    d_destructp (fun t => {A: ("Fs'" $ "Fn", "Fors", "Fois") = t}).
    d_forallp "m"; d_forallp "c"; d_forallp "n'".
    d_splitp. d_swap. d_substp. d_evalp.
    d_destructp (fun t => {A: ("Fs'" $ "Fn", "Fors", "Fois") = t}).

    d_orp.
    (* for true *)
    d_splitp. d_swap. d_substp. d_eval.
    d_destructtuplep
      {t: "Fs'" $ "Fn"} {t: "Fors"} {t: "Fois"}
      {t: ("c", CNil)}
      {t:  CNil} {t: CNil}; do 2 d_splitp.
    d_ifc. d_substp. d_splitp. d_swap.
    eapply DSCut; first by eapply DAPInNil.
    d_forallp {t: (CPLDeliver $ "n'" $ "m")}.
    eapply DSCut; first by eapply DSNotImpliesFalse with (Ac := {A: (CPLDeliver $ "n'" $ "m") \in CNil}).
    d_swap; eapply DARewriteIffPL; first by d_head.
    rewrite_assertion_any; d_swap; d_clear.
    d_ifp. d_head. d_false.
    (* for false *)
    d_splitp. d_swap. d_substp. d_eval.
    d_destructtuplep
      {t: "Fs'" $ "Fn"} {t: "Fors"} {t: "Fois"}
      {t: (CPair $ "c" $ (FUnion $ CNil $ (CCons $ (CPair $ "n'" $ "c") $ CNil)))}
      {t:  CNil} {t: (CCons $ (CPLDeliver $ "n'" $ "m") $ CNil)}. do 2 d_splitp.
    d_ifc. d_splitp. d_rotate 2. d_substp. d_subst.
    d_splitc. d_eval.
    (* DEBUG: FUnion not working here *)
    d_use DAPInUnion.
    d_forallp {t: CNil}. d_forallp {t: (CCons $ (CPair $ "n'" $ "c") $ CNil)}.
    d_forallp {t: CPair $ "n'" $ "c"}.
    d_ifp. d_right.
    eapply DAPIn. by []. by [].
    d_head.
    d_splitc. eapply DAPEqual. by [].
    d_rotate 4.
    d_destructpairp {t: "i"} {t: "e"} {t: 0} {t: (CSLDeliver $ "n'" $ (CPair $ "c" $ "m"))}. rewrite_assertion_any.
    d_splitp. d_rotate 3. d_subst. d_splitp. d_splitc. d_head. d_swap. d_splitp.
    d_splitc. d_head. d_swap. d_head.

    (* periodic *)
    d_ifp. d_ifc. d_splitp. d_swap. d_subst. d_eval.
    d_destructtuplep
      {t: "Fs'" $ "Fn"} {t: "Fors"} {t: "Fois"}
      {t: ("Fs" $ "Fn")}
      {t:  CNil} {t: CNil}. do 2 d_splitp.
    d_ifc. d_subst.
    d_splitp. d_swap.
    eapply DSCut; first by eapply DAPInNil.
    d_forallp {t: (CPLDeliver $ "n'" $ "m")}.
    eapply DSCut; first by eapply DSNotImpliesFalse with (Ac := {A: (CPLDeliver $ "n'" $ "m") \in CNil}).
    d_swap; eapply DARewriteIffPL; first by d_head.
    rewrite_assertion_any; d_swap; d_clear.
    d_ifp. d_head. d_false.

    d_head.
  }

  (* by lemma 87 *)
  d_have {A:
            self (
                "Fn" = "n" /\ (CPLDeliver $ "n'" $ "m" \in "Fois") =>>
                                                                     (("n'", "c") \in (FRight $ ("Fs'" $ "n"))) /\ eventuallyp (on "n", event[0]<- CSLDeliver $ "n'" $ ("c", "m"))
              )
         }.
  {
    eapply DARewriteEntailsP with (Arp := {A: (on "n", event[0]<- CSLDeliver $ "n'" $ ("c", "m"))})
                                  (Arc := {A: eventuallyp (on "n", event[0]<- CSLDeliver $ "n'" $ ("c", "m"))}).
    eapply DTL87.
    rewrite_assertion_pos.
    d_head.
  }

  (* by lemma 43 *)
  d_have {A:
            self (CPair $ "n'" $ "c" \in FRight $ ("Fs" $ "n") /\ eventuallyp on "n", event [0]<- CSLDeliver $ "n'" $ (CPair $ "c" $ "m") =>>
                                                                                            "Fn" = "n" -> CPLDeliver $ "n'" $ "m" \notin "Fois")
         }.
  {
    do 2 d_clear.
    d_use L43.
    d_head.
  }

  (* by InvSSe *)
  d_have {A:
            self (
                CPair $ "n'" $ "c" \in FRight $ ("Fs" $ "n") =>>
                                              always (CPair $ "n'" $ "c" \in FRight $ ("Fs" $ "n"))
         )}.
  {
    set S := fun ts => {A: ("n'", "c") \in FRight $ ts}.
    eapply DSCut; first by apply DPInvSSe with (S := S).
    d_forallp "n".

    (* request *)
    d_ifp. d_forallc "s". d_forallc "e". d_ifc.

    (*
    eapply DARewriteIffPL; first by
        d_use DAPConcatIn; d_forallp {t: ("n'", "c")}; d_forallp {t: FRight $ "s"}.
    rewrite_assertion_any.

    d_existsp "sl"; d_existsp "sr"; d_evalc.
     *)
    d_eval.
    d_destructc (fun t => {A: ("n'", "c") \in
                              match: match: t with: {{(#, %, %) -> P 0 0}} with: {{(%, #) -> #(0, 0)}}}).
    d_forallc "r"; d_forallc "c".
    d_ifc; d_substc; d_evalc.

    d_destructc (fun t => {A: ("n'", "c") \in
                              match: match: t with: {{(#, %, %) -> #(0, 0)}}  with: {{(%, #) -> P 0 0}}}).
    d_forallc "m"; d_forallc "n'".
    d_ifc; d_substc; d_evalc.
    d_rotate 2. d_subst. d_eval. d_head.

    (* indication *)
    d_ifp. d_forallc "s". d_forallc "i". d_forallc "e". d_ifc.
    d_eval.
    d_destructc (fun t => {A: ("n'", "c") \in
                              match: match: t with: {{(#, %, %) -> P 0 0}} with: {{(%, #) -> #(0, 0)}}}).
    d_forallc "?r"; d_forallc "?c".
    d_ifc. d_subst. d_eval.
    d_destructc (fun t => {A: ("n'", "c") \in
                              match: match: t with: {{(#, %, %) -> #(0, 0)}}  with: {{(%, #) -> P 0 0}}}).
    d_forallc "m"; d_forallc "c"; d_forallc "n'".
    d_ifc. d_subst. d_eval.

    d_rotate 2. d_subst. d_eval.
    eapply DSCut; first by apply DAPInEliminateTrue.
    d_forallp {t: (CPair $ "n'" $ "c")}.
    d_forallp "?r".
    d_eval. d_splitp. d_clear. d_ifp. d_head.
    d_subst. d_eval. d_swap. d_head.

    (* periodic *)
    d_ifp. d_forallc "s".
    d_ifc. d_subst. d_eval. d_head.

    d_head.
  }

  (* by lemma 104 *)
  d_have {A:
            self (
                eventuallyp ( on "n", event [0]<- CSLDeliver $ "n'" $ (CPair $ "c" $ "m")) =>>
                            always (eventuallyp ( on "n", event [0]<- CSLDeliver $ "n'" $ (CPair $ "c" $ "m")))
         )}.
  {
    set A := {A:  eventuallyp ( on "n", event [0]<- CSLDeliver $ "n'" $ (CPair $ "c" $ "m"))}.
    d_have {A:
              (A =>> always A) -> self (A =>> always A)
           }.
    eapply DTL129.
    d_ifp. eapply DTL104. d_head.
  }

  (* by (3) and (4) *)
  d_have {A:
            self (
                (CPair $ "n'" $ "c" \in FRight $ ("Fs" $ "n")) /\ eventuallyp on "n", event [0]<- CSLDeliver $ "n'" $ (CPair $ "c" $ "m") =>>
                                                                                            always ((CPair $ "n'" $ "c" \in FRight $ ("Fs" $ "n")) /\ eventuallyp on "n", event [0]<- CSLDeliver $ "n'" $ (CPair $ "c" $ "m"))
         )}.
  {
    set A := {A: CPair $ "n'" $ "c" \in FRight $ ("Fs" $ "n")}.
    set B := {A: eventuallyp on "n", event [0]<- CSLDeliver $ "n'" $ (CPair $ "c" $ "m")}.
    d_have {A:
              (A =>> always A) /\ (B =>> always B) ->
              (A /\ B =>> (always A) /\ (always B))
           }.
    {
      d_ifc.
      d_splitp.
      d_splitc. d_ifc. d_splitp.  d_rotate 2. d_splitp. d_swap; d_clear.
      d_swap. d_splitp. d_swap; d_clear. d_ifp. d_rotate 7. d_head. d_swap. d_ifp.
      d_rotate 6. d_head.
      d_splitc. d_head. d_swap. d_head.
      d_splitp. d_clear. d_swap. d_splitp. d_clear.
      d_have {A:
                (A -> always A) /\ (B -> always B) ->
                (A /\ B -> always A /\ always B)
             }.
      {
        d_ifc. d_ifc. d_swap. d_splitp. d_ifp.  d_swap. d_splitp. d_head.
        d_splitc. d_head.
        d_swap. d_ifp.  d_swap. d_splitp.  d_swap. d_head. d_head.
      }
      eapply DARewriteIfC with (Arp := {A: (A -> always A) /\ (B -> always B)})
                               (Arc := {A: A /\ B -> always A /\ always B}).
      d_head. rewrite_assertion_pos.
      eapply DARewriteCongruentCL; first by eapply DTL128_3 with (A := {A: (A -> always A)})
                                                                 (B := {A: (B -> always B)}).
      rewrite_assertion_any.
      d_splitc. d_rotate 2. d_head.
      d_swap. d_head.
    }

    eapply DARewriteCongruentPR with (Arc := {A: always A /\ always B})
                                  (Arp := {A: always (A /\ B)}).
    eapply DTL128_1. rewrite_assertion_any.
    set A1 := {A: CPair $ "n'" $ "c" \in FRight $ ("Fs" $ "n")}.
    set B1 := {A: eventuallyp on "n", event [0]<- CSLDeliver $ "n'" $ (CPair $ "c" $ "m")}.
    eapply DARewriteIfC; first by d_head. rewrite_assertion_pos.
    eapply DARewriteIffCL with (Arp := {A:  self ((A1 =>> always A1) /\ (B1 =>> always B1))})
                               (Arc := {A: self ((A1 =>> always A1)) /\ self ((B1 =>> always B1))}).
    eapply DTL130. rewrite_assertion_any.
    d_splitc. d_rotate 2. d_head. d_swap. d_head.
  }

  (* by lemma 97 on (5) and (2) *)
  d_have {A:
            self (
                CPair $ "n'" $ "c" \in FRight $ ("Fs" $ "n") /\ eventuallyp on "n", event [0]<- CSLDeliver $ "n'" $ (CPair $ "c" $ "m") =>>
                              always ("Fn" = "n" -> CPLDeliver $ "n'" $ "m" \notin "Fois")
              )
         }.
  {
    set A := {A: CPair $ "n'" $ "c" \in FRight $ ("Fs" $ "n")}.
    set B := {A: eventuallyp on "n", event [0]<- CSLDeliver $ "n'" $ (CPair $ "c" $ "m")}.
    set D := {A: ("Fn" = "n" -> CPLDeliver $ "n'" $ "m" \notin "Fois")}.
    d_have {A:
              self ((A /\ B =>> always (A /\ B)) /\ (A /\ B =>> D) ->
              (A /\ B =>> always D))
           }.
    {
      d_have {A:
                ((A /\ B =>> always (A /\ B)) /\ (A /\ B =>> D) -> A /\ B =>> always D) -> self ((A /\ B =>> always (A /\ B)) /\ (A /\ B =>> D) -> A /\ B =>> always D)
             }.
      eapply DTL129.

      d_ifp.
      eapply DTL97 with (A1 := {A: A /\ B})
                        (A2 := {A: A /\ B})
                        (A3 := {A: D}).
      d_head.
    }
    eapply DSCut; first by apply DTL131 with (A := {A: (A /\ B =>> always (A /\ B)) /\ (A /\ B =>> D)})
                                             (B := {A: A /\ B =>> always D}).
    d_ifp. d_head.
    d_ifp.

    eapply DARewriteIffCL; first by eapply DTL130 with (A := {A: (A /\ B =>> always (A /\ B))})
                                                       (B := {A: (A /\ B =>> D)}).
    rewrite_assertion_any.
    d_splitc. d_swap. d_head.
    d_rotate 4. d_head.
    d_head.
  }

  (* by rule ASASe on (1) and (6) *)
  d_have {A:
           self (("Fn" = "n" /\ CPLDeliver $ "n'" $ "m" \in "Fois") =>>
                                                               always^ ("Fn" = "n" -> CPLDeliver $ "n'" $ "m" \notin "Fois"))
         }.
  {
    set S := fun ts => {A: ("n'", "c") \in (FRight $ ts) /\ eventuallyp on "n", event [0]<- CSLDeliver $ "n'" $ (CPair $ "c" $ "m")}.
    eapply DSCut; first by eapply DPASASe with (S := S)
                               (A := {A: "Fn" = "n" /\ CPLDeliver $ "n'" $ "m" \in "Fois"})
                               (A' := {A: ("Fn" = "n" -> CPLDeliver $ "n'" $ "m" \notin "Fois")}).
    d_forallp "n".
    d_ifp. d_rotate 5. d_head.
    d_ifp. d_head.
    d_head.
  }

  d_have {A:
            ("Fn" = "n" -> CPLDeliver $ "n'" $ "m" \notin "Fois") ->
            ~("Fn" = "n" /\ CPLDeliver $ "n'" $ "m" \in "Fois")
         }.
  {
    d_ifc. d_notc. d_splitp. d_rotate 2. d_ifp. d_rotate 8. d_head.
    d_subst. d_notp. d_rotate 9. d_head.
  }

  d_swap. eapply DARewriteIfP; first by d_head. rewrite_assertion_pos.
  set P := {A: ("Fn" = "n" /\ CPLDeliver $ "n'" $ "m" \in "Fois")}.
  d_have {A:
            self (P =>> alwaysp^ (~ P))
         }.
  {
    eapply DARewriteIfP; first by apply DTL105_1 with (A := P). rewrite_assertion_pos.
    d_head.
  }

  d_have {A:
            self (
                P =>> always^ (~ P) /\ alwaysp^ (~ P)
              )
         }.
  {
    d_have {A:
              (P =>> always^ (~ P)) /\ (P =>> alwaysp^ (~ P)) ->
              (P =>> always^ (~ P) /\ alwaysp^ (~ P))
           }.
    {
      d_ifc.
      d_splitp. d_splitc. d_ifc. d_swap. d_splitp. d_splitc. d_ifp. d_swap. d_head.
      d_head. do 2 d_clear. d_swap. d_splitp. d_swap; d_clear. d_ifp. d_head. d_head.
      d_have {A:
                ((P -> always^ ~P) /\ (P -> alwaysp^ ~P)) ->
                (P ->  (always^ (~ P) /\ alwaysp^ (~ P)))
             }.
      {
        d_ifc. d_ifc. d_swap. d_splitp. d_ifp. d_swap. d_head.
        d_splitc. d_head.
        d_swap. d_ifp. d_swap. d_head. d_head.
      }
      eapply DARewriteIfC with (Arp := {A: (P -> always^ ~P) /\ (P -> alwaysp^ ~P)})
                               (Arc := {A: (P -> (always^ (~ P) /\ alwaysp^ (~ P)))}).
      d_head. rewrite_assertion_pos.
      eapply DARewriteCongruentCL; first by eapply DTL128_3 with (A := {A: P -> always^ ~P})
                                                                 (B := {A: (P -> alwaysp^ (~ P))}).
      rewrite_assertion_any.
      d_ifp. d_splitc. d_splitp; d_swap; d_clear. d_head.
      d_swap. d_splitp; d_swap; d_clear. d_head.
      d_splitc. d_swap. d_splitp. d_swap. d_head.
      d_rotate 2. d_splitp. d_swap. d_head.
    }

    eapply DARewriteIfC; first by d_head. rewrite_assertion_pos.
    eapply DARewriteIffCL with (Arp := {A: self ((P =>> always^ (~ P)) /\ (P =>> alwaysp^ (~ P)))})
                               (Arc := {A: self ((P =>> always^ (~ P))) /\ self ((P =>> alwaysp^ (~ P)))}).
    eapply DTL130. rewrite_assertion_any.
    d_splitc. d_rotate 2. d_head. d_swap. d_head.
  }
  d_have {A:
            ~("Fn" = "n" /\ CPLDeliver $ "n'" $ "m" \in "Fois") ->
            ("Fn" = "n" -> CPLDeliver $ "n'" $ "m" \notin "Fois")
         }.
  {
    d_ifc.
    d_subst.
    d_ifc.
    d_notc.  d_rotate 2. d_notp. d_splitc. d_rotate 12. d_head.
    d_rotate 11. d_head.
  }
  d_swap.
  set P1 := {A: ("Fn" = "n" /\ CPLDeliver $ "n'" $ "m" \in "Fois")}.

  eapply DARewriteIfC with (Arp := {A: ~ P1})
                           (Arc := {A: "Fn" = "n" -> CPLDeliver $ "n'" $ "m" \notin "Fois"}).
  d_swap. d_head.
  rewrite_assertion_pos.
  d_head.
Qed.

Lemma L44 :
  Context
    [:: V "c'"; V "c"; V "m"; V "n'"; V "n"]
    [:: {A: on "n'", event[]-> CPLSend $ "n" $ "m" =>> alwaysp^ (~ on "n'", event[]-> CPLSend $ "n" $ "m")}; {A: correct "n"}; {A: correct "n'"}] |- perfect_link, {A:
    self (
      on "n", event [0]<- CSLDeliver $ "n'" $ ("c", "m") /\
      eventuallyp on "n", event [0]<- CSLDeliver $ "n'" $ ("c'", "m") =>>
      "c" = "c'"
    )
  }.
Proof.
  (* by SL'2 *)
  d_have {A:
            forall: "n0", "n0'", "m0":
    on "n0", event [0]<- CSLDeliver $ "n0'" $ "m0" <~
                   on "n0'", event [0]-> CSLSend $ "n0" $ "m0"
         }.
  {
    do 3 d_clear. d_clearv "c'"; d_clearv "c"; d_clearv "m"; d_clearv "n'"; d_clearv "n".
    d_use PL_SL_2.
    d_head.
  }
  d_forallp "n"; d_forallp "n'"; d_forallp {t: ("c", "m")}.

  (* by OR' *)
  d_have {A:
            (on "n'", event [0]-> CSLSend $ "n" $ (CPair $ "c" $ "m")) =>>
                                                                          eventuallyp (on "n'", ((0, (CSLSend $ "n" $ (CPair $ "c" $ "m"))) \in "Fors") /\ self-event)
         }.
  {
    d_swap; d_clear.
    d_use DPOR'.
    d_forallp "n'". d_forallp 0. d_forallp {t: CSLSend $ "n" $ (CPair $ "c" $ "m")}.
    eapply DARewriteIfP with (Arp := {A:
                                        self-event /\ "Fn" = "n'" /\ CPair $ 0 $ (CSLSend $ "n" $ (CPair $ "c" $ "m")) \in "Fors"})
                             (Arc := {A:
                                        (on "n'", ((0, (CSLSend $ "n" $ (CPair $ "c" $ "m"))) \in "Fors") /\ self-event)}).
    {
      d_ifc. d_splitc. d_splitp. d_swap. d_splitp. d_swap. d_splitc. d_swap. d_head.
      d_head. d_splitp. d_head.
    }
    rewrite_assertion_pos.
    eapply DARewriteIfP; first by apply DTL123 with (A := {A:
                                                             (on "n'", ((0, (CSLSend $ "n" $ (CPair $ "c" $ "m"))) \in "Fors") /\ self-event)}).
    rewrite_assertion_pos.
    d_head.
  }

  (* by InvL *)
  d_have {A:
            (on "n'", ((0, (CSLSend $ "n" $ (CPair $ "c" $ "m"))) \in "Fors") /\ self-event) =>>
                                                                                             ((on "n'", event[]-> CPLSend $ "n" $ "m") /\ (FLeft $ ("Fs'" $ "n") = "c"))
         }.
  {
    eapply DSCut; first by apply DPInvL with (A := {A:
         on "n'", ((0, CSLSend $ "n" $ ("c", "m")) \in "Fors") ->
                 ((on "n'", event[]-> CPLSend $ "n" $ "m") /\ (FLeft $ ("Fs'" $ "n") = "c"))});
    first by repeat constructor.
    (* prove request *)
    d_ifp. d_forallc "e".
    d_ifc; d_splitp. d_swap; d_evalp.
    d_destructp (fun t => {A: ("Fs'" $ "Fn", "Fors", "Fois") = t});
      d_forallp "r"; d_forallp "c"; d_splitp; d_swap;
        d_substp; d_evalp.
    d_destructp (fun t => {A: ("Fs'" $ "Fn", "Fors", "Fois") = t});
      d_forallp "m"; d_forallp "n"; d_splitp; d_swap;
            d_substp; d_evalp.
    d_destructtuplep
      {t: "Fs'" $ "Fn"} {t: "Fors"} {t: "Fois"}
      {t: ((FSucc $ "c"), "r")}
      {t: [(0, CSLSend $ "n" $ (FSucc $ "c", "m"))]}
      {t: CNil}.
    do 2 d_splitp.
    d_ifc. d_splitp.
    d_swap. d_subst.
    d_have {A:
              (CPair $ 0 $ (CSLSend $ "n" $ (CPair $ "c" $ "m")) \in CCons $ (CPair $ 0 $ (CSLSend $ "n" $ (CPair $ (FSucc $ "c") $ "m"))) $ CNil) -> AFalse}.
    {
      d_use DAPNotInCons.
      d_forallp {t: CPair $ 0 $ (CSLSend $ "n" $ (CPair $ "c" $ "m"))}.
      d_forallp {t: (CPair $ 0 $ (CSLSend $ "n" $ (CPair $ (FSucc $ "c") $ "m")))}.
      d_forallp {t: CNil}.
      d_splitp.  d_clear.
      d_ifp. d_splitc. d_notc.
      eapply DSEqualEvent. d_splitp; d_clear.
      eapply DSEqualEvent. d_splitp. d_clear.
      eapply DSCut; first by eapply DAPNotEqualToSucc.
      d_forallp "c".
      d_ifp.
      d_destructpairp {t: "c"} {t: "m"} {t: FSucc $ "c"} {t: "m"}.
      rewrite_assertion_any. d_splitp. d_head.
      d_false.
      d_notc.
      eapply DSCut; first by eapply DAPInNil.
      d_forallp {t: CPair $ 0 $ (CSLSend $ "n" $ (CPair $ "c" $ "m"))}.
      eapply DSCut; first by eapply DSNotImpliesFalse with (Ac := {A:
                                                                     CPair $ 0 $ (CSLSend $ "n'" $ (CPair $ "c" $ "m")) \in CNil}).
      d_swap; eapply DARewriteIffPL; first by d_head.
      rewrite_assertion_any; d_swap; d_clear.
      d_notp. d_head. d_ifc. d_swap. d_notp. d_head.
    }
    d_ifp. d_head. d_false.

    (* prove indication *)
    d_ifp. d_forallc "i". d_forallc "e".
    d_ifc; d_splitp. d_swap. d_evalp.
    d_destructp (fun t => {A: ("Fs'" $ "Fn", "Fors", "Fois") = t}).
    d_forallp "r"; d_forallp "c". d_splitp; d_swap;
      d_substp. d_evalp.
    d_destructp (fun t => {A: ("Fs'" $ "Fn", "Fors", "Fois") = t}).
    d_forallp "m'". d_forallp "c'". d_forallp "n'". d_splitp. d_swap.
    d_substp.
    d_evalp.
    d_destructp (fun t => {A: ("Fs'" $ "Fn", "Fors", "Fois") = t}).
    d_orp.

    d_splitp. d_swap. d_substp. d_eval.
    d_ifc. d_swap.
    d_destructtuplep
      {t: "Fs'" $ "Fn"} {t: "Fors"} {t: "Fois"}
      {t: ("c", "r")}
      {t: CNil}
      {t: CNil}; do 2 d_splitp. d_rotate 3. d_splitp. d_swap. d_subst.
    eapply DSCut; first by eapply DAPInNil.
    d_forallp {t: CPair $ 0 $ (CSLSend $ "n" $ (CPair $ "c" $ "m"))}.
    eapply DSCut; first by eapply DSNotImpliesFalse with (Ac := {A:
                                                                   CPair $ 0 $ (CSLSend $ "n" $ (CPair $ "c" $ "m")) \in CNil}).
    d_swap; eapply DARewriteIffPL; first by d_head.
    rewrite_assertion_any; d_swap; d_clear.
    d_ifp. d_head. d_false.

    d_splitp. d_swap. d_substp. d_eval.
    d_ifc. d_swap.
    d_destructtuplep
      {t: "Fs'" $ "Fn"} {t: "Fors"} {t: "Fois"}
      {t: (CPair $ "c" $ (FUnion $ "r" $ (CCons $ (CPair $ "n'" $ "c'") $ CNil)))}
      {t: CNil}
      {t: (CCons $ (CPLDeliver $ "n'" $ "m'") $ CNil)}.
    do 2 d_splitp. d_rotate 3. d_splitp. d_swap. d_substp.
    eapply DSCut; first by eapply DAPInNil.
    d_forallp {t: CPair $ 0 $ (CSLSend $ "n" $ (CPair $ "c" $ "m"))}.
    eapply DSCut; first by eapply DSNotImpliesFalse with (Ac := {A:
                                                                   CPair $ 0 $ (CSLSend $ "n" $ (CPair $ "c" $ "m")) \in CNil}).
    d_swap; eapply DARewriteIffPL; first by d_head.
    rewrite_assertion_any; d_swap; d_clear.
    d_ifp. d_head. d_false.

    (* prove for periodic *)
    d_ifp. d_ifc. d_splitp. d_swap. d_eval.
    d_destructtuplep
      {t: "Fs'" $ "Fn"} {t: "Fors"} {t: "Fois"}
      {t: "Fs" $ "Fn"}
      {t: CNil}
      {t: CNil}; do 2 d_splitp. d_ifc. d_splitp. d_swap.
    d_subst.
    eapply DSCut; first by eapply DAPInNil.
    d_forallp {t: CPair $ 0 $ (CSLSend $ "n" $ (CPair $ "c" $ "m"))}.
    eapply DSCut; first by eapply DSNotImpliesFalse with (Ac := {A:
                                                                   CPair $ 0 $ (CSLSend $ "n" $ (CPair $ "c" $ "m")) \in CNil}).
    d_swap; eapply DARewriteIffPL; first by d_head.
    rewrite_assertion_any; d_swap; d_clear.
    d_ifp. d_head. d_false.

    d_splitp. d_swap; d_clear.
    eapply DTGeneralization; first by repeat constructor.
    d_ifc. d_splitp. d_rotate 2. d_ifp. d_rotate 4. d_swap. d_rotate 2. d_head.
    d_ifp. d_rotate 5. d_head.
    d_head.
  }

  (* by lemma 86 and lemma 96 on (1), (2), and (3) *)
  d_have {A:
            ("Fn" = "n" /\ "Fd" = CCons $ 0 $ CNil /\ "Fo" = OIndication /\ "Fe" = CSLDeliver $ "n'" $ (CPair $ "c" $ "m")) =>>
                                                                                                                            eventuallyp (on "n'", event []-> CPLSend $ "n" $ "m" /\ FLeft $ ("Fs'" $ "n") = "c")
         }.
  {
    eapply DSCut; first by eapply DTL96_2 with (A1 := {A:
                                  ("Fn" = "n" /\ "Fd" = CCons $ 0 $ CNil /\ "Fo" = OIndication /\ "Fe" = CSLDeliver $ "n'" $ (CPair $ "c" $ "m"))})
                        (A2 := {A:
                                  ("Fn" = "n'" /\ "Fd" = CCons $ 0 $ CNil /\ "Fo" = ORequest /\ "Fe" = CSLSend $ "n" $ (CPair $ "c" $ "m"))})
                        (A3 := {A:
                                  (eventuallyp (on "n'", (CPair $ 0 $ (CSLSend $ "n" $ (CPair $ "c" $ "m")) \in "Fors") /\ self-event))}).
    d_ifp. d_splitc. d_rotate 2. d_head.
    d_swap. d_head.
    eapply DARewriteCongruentPR; first by apply DTL83_1 with (A := {A: (on "n'", (CPair $ 0 $ (CSLSend $ "n" $ (CPair $ "c" $ "m")) \in "Fors") /\ self-event)}).
    rewrite_assertion_any.

    eapply DSCut; first by eapply DTL96_2 with (A1 := {A:
                                  ("Fn" = "n" /\ "Fd" = CCons $ 0 $ CNil /\ "Fo" = OIndication /\ "Fe" = CSLDeliver $ "n'" $ (CPair $ "c" $ "m"))})
                        (A2 := {A:
                                  on "n'", (CPair $ 0 $ (CSLSend $ "n" $ (CPair $ "c" $ "m")) \in "Fors") /\ self-event})
                        (A3 := {A:
                                  on "n'", event []-> CPLSend $ "n" $ "m" /\ FLeft $ ("Fs'" $ "n") = "c"}).
    d_ifp. d_splitc. d_head.
    d_swap. d_head.
    d_head.
  }

  (* by rule SInv on (4) *)
  d_have {A:
            self (
                ("Fn" = "n" /\ "Fd" = CCons $ 0 $ CNil /\ "Fo" = OIndication /\ "Fe" = CSLDeliver $ "n'" $ (CPair $ "c" $ "m")) =>> eventuallyp (on "n'", event []-> CPLSend $ "n" $ "m" /\ FLeft $ ("Fs'" $ "n") = "c")
              )
         }.
  {
    eapply DARewriteIfP with (Arp := {A:
                                          (self (("Fn" = "n" /\ "Fd" = CCons $ 0 $ CNil /\ "Fo" = OIndication /\ "Fe" = CSLDeliver $ "n'" $ (CPair $ "c" $ "m")) =>> eventuallyp (on "n'", event []-> CPLSend $ "n" $ "m" /\ FLeft $ ("Fs'" $ "n") = "c")))})
                               (Arc := {A: restrict_assertion {A: self-event} (("Fn" = "n" /\ "Fd" = CCons $ 0 $ CNil /\ "Fo" = OIndication /\ "Fe" = CSLDeliver $ "n'" $ (CPair $ "c" $ "m")) =>> eventuallyp (on "n'", event []-> CPLSend $ "n" $ "m" /\ FLeft $ ("Fs'" $ "n") = "c"))}).

    eapply DPSInv_1.
    rewrite_assertion_pos.

    d_have {A:
              ("Fn" = "n" /\ "Fd" = CCons $ 0 $ CNil /\ "Fo" = OIndication /\ "Fe" = CSLDeliver $ "n'" $ (CPair $ "c" $ "m") <~
                        ("Fn" = "n'" /\ "Fd" = CNil /\ "Fo" = ORequest /\ "Fe" = CPLSend $ "n" $ "m") /\ FLeft $ ("Fs'" $ "n") = "c") -> self ("Fn" = "n" /\ "Fd" = CCons $ 0 $ CNil /\ "Fo" = OIndication /\ "Fe" = CSLDeliver $ "n'" $ (CPair $ "c" $ "m") <~
                        ("Fn" = "n'" /\ "Fd" = CNil /\ "Fo" = ORequest /\ "Fe" = CPLSend $ "n" $ "m") /\ FLeft $ ("Fs'" $ "n") = "c")
           }.
    {
      eapply DTL129.
    }
    d_ifp. d_head. d_head.
  }

  (* similarly for c' *)
  d_have {A:
             (
                ("Fn" = "n" /\ "Fd" = CCons $ 0 $ CNil /\ "Fo" = OIndication /\ "Fe" = CSLDeliver $ "n'" $ (CPair $ "c'" $ "m")) =>> eventuallyp (on "n'", event []-> CPLSend $ "n" $ "m" /\ FLeft $ ("Fs'" $ "n") = "c'")
              )
         }.
  {
    do 5 d_clear.
    d_have {A:
              forall: "n0", "n0'", "m0":
                                     on "n0", event [0]<- CSLDeliver $ "n0'" $ "m0" <~
                                                    on "n0'", event [0]-> CSLSend $ "n0" $ "m0"
           }.
    {
      do 3 d_clear. d_clearv "c'"; d_clearv "c"; d_clearv "m"; d_clearv "n'"; d_clearv "n".
      d_use PL_SL_2.
      d_head.
    }
    d_forallp "n"; d_forallp "n'"; d_forallp {t: ("c'", "m")}.

    (* by OR' *)
    d_have {A:
              (on "n'", event [0]-> CSLSend $ "n" $ (CPair $ "c'" $ "m")) =>>
                                                                         eventuallyp (on "n'", ((0, (CSLSend $ "n" $ (CPair $ "c'" $ "m"))) \in "Fors") /\ self-event)
           }.
    {
      d_use DPOR'.
      d_forallp "n'". d_forallp 0. d_forallp {t: CSLSend $ "n" $ (CPair $ "c'" $ "m")}.
      eapply DARewriteIfP with (Arp := {A:
                                          self-event /\ "Fn" = "n'" /\ CPair $ 0 $ (CSLSend $ "n" $ (CPair $ "c'" $ "m")) \in "Fors"})
                               (Arc := {A:
                                          (on "n'", ((0, (CSLSend $ "n" $ (CPair $ "c'" $ "m"))) \in "Fors") /\ self-event)}).
      {
        d_ifc. d_splitc. d_splitp. d_swap. d_splitp. d_swap. d_splitc. d_swap. d_head.
        d_head. d_splitp. d_head.
      }
      rewrite_assertion_pos.
      eapply DARewriteIfP; first by apply DTL123 with (A := {A:
                                                               (on "n'", ((0, (CSLSend $ "n" $ (CPair $ "c'" $ "m"))) \in "Fors") /\ self-event)}).
      rewrite_assertion_pos.
      d_head.
    }
    (* by InvL *)
    d_have {A:
              (on "n'", ((0, (CSLSend $ "n" $ (CPair $ "c'" $ "m"))) \in "Fors") /\ self-event) =>>
                                                                                                ((on "n'", event[]-> CPLSend $ "n" $ "m") /\ (FLeft $ ("Fs'" $ "n") = "c'"))
           }.
    {
      eapply DSCut; first by apply DPInvL with (A := {A:
                                                        on "n'", ((0, CSLSend $ "n" $ ("c'", "m")) \in "Fors") ->
                                                                 ((on "n'", event[]-> CPLSend $ "n" $ "m") /\ (FLeft $ ("Fs'" $ "n") = "c'"))});
      first by repeat constructor.
      (* prove request *)
      d_ifp. d_forallc "e".
      d_ifc; d_splitp. d_swap; d_evalp.
      d_destructp (fun t => {A: ("Fs'" $ "Fn", "Fors", "Fois") = t});
        d_forallp "r"; d_forallp "c'"; d_splitp; d_swap;
          d_substp; d_evalp.
      d_destructp (fun t => {A: ("Fs'" $ "Fn", "Fors", "Fois") = t});
        d_forallp "m"; d_forallp "n"; d_splitp; d_swap;
          d_substp; d_evalp.
      d_destructtuplep
        {t: "Fs'" $ "Fn"} {t: "Fors"} {t: "Fois"}
        {t: ((FSucc $ "c'"), "r")}
        {t: [(0, CSLSend $ "n" $ (FSucc $ "c'", "m"))]}
        {t: CNil}.
      do 2 d_splitp.
      d_ifc. d_splitp.
      d_swap. d_subst.
      d_have {A:
                (CPair $ 0 $ (CSLSend $ "n" $ (CPair $ "c'" $ "m")) \in CCons $ (CPair $ 0 $ (CSLSend $ "n" $ (CPair $ (FSucc $ "c'") $ "m"))) $ CNil) -> AFalse}.
      {
        d_use DAPNotInCons.
        d_forallp {t: CPair $ 0 $ (CSLSend $ "n" $ (CPair $ "c'" $ "m"))}.
        d_forallp {t: (CPair $ 0 $ (CSLSend $ "n" $ (CPair $ (FSucc $ "c'") $ "m")))}.
        d_forallp {t: CNil}.
        d_splitp.  d_clear.
        d_ifp. d_splitc. d_notc.
        eapply DSEqualEvent. d_splitp; d_clear.
        eapply DSEqualEvent. d_splitp. d_clear.
        eapply DSCut; first by eapply DAPNotEqualToSucc.
        d_forallp "c'".
        d_ifp.
        d_destructpairp {t: "c'"} {t: "m"} {t: FSucc $ "c'"} {t: "m"}.
        rewrite_assertion_any. d_splitp. d_head.
        d_false.
        d_notc.
        eapply DSCut; first by eapply DAPInNil.
        d_forallp {t: CPair $ 0 $ (CSLSend $ "n" $ (CPair $ "c'" $ "m"))}.
        eapply DSCut; first by eapply DSNotImpliesFalse with (Ac := {A:
                                                                       CPair $ 0 $ (CSLSend $ "n'" $ (CPair $ "c'" $ "m")) \in CNil}).
        d_swap; eapply DARewriteIffPL; first by d_head.
        rewrite_assertion_any; d_swap; d_clear.
        d_notp. d_head. d_ifc. d_swap. d_notp. d_head.
      }
      d_ifp. d_head. d_false.

      (* prove indication *)
      d_ifp. d_forallc "i". d_forallc "e".
      d_ifc; d_splitp. d_swap. d_evalp.
      d_destructp (fun t => {A: ("Fs'" $ "Fn", "Fors", "Fois") = t}).
      d_forallp "r"; d_forallp "c'". d_splitp; d_swap;
                                       d_substp. d_evalp.
      d_destructp (fun t => {A: ("Fs'" $ "Fn", "Fors", "Fois") = t}).
      d_forallp "m'". d_forallp "c''". d_forallp "n'". d_splitp. d_swap.
      d_substp.
      d_evalp.
      d_destructp (fun t => {A: ("Fs'" $ "Fn", "Fors", "Fois") = t}).
      d_orp.

      d_splitp. d_swap. d_substp. d_eval.
      d_ifc. d_swap.
      d_destructtuplep
        {t: "Fs'" $ "Fn"} {t: "Fors"} {t: "Fois"}
        {t: ("c'", "r")}
        {t: CNil}
        {t: CNil}; do 2 d_splitp. d_rotate 3. d_splitp. d_swap. d_subst.
      eapply DSCut; first by eapply DAPInNil.
      d_forallp {t: CPair $ 0 $ (CSLSend $ "n" $ (CPair $ "c'" $ "m"))}.
      eapply DSCut; first by eapply DSNotImpliesFalse with (Ac := {A:
                                                                     CPair $ 0 $ (CSLSend $ "n" $ (CPair $ "c'" $ "m")) \in CNil}).
      d_swap; eapply DARewriteIffPL; first by d_head.
      rewrite_assertion_any; d_swap; d_clear.
      d_ifp. d_head. d_false.

      d_splitp. d_swap. d_substp. d_eval.
      d_ifc. d_swap.
      d_destructtuplep
        {t: "Fs'" $ "Fn"} {t: "Fors"} {t: "Fois"}
        {t: (CPair $ "c'" $ (FUnion $ "r" $ (CCons $ (CPair $ "n'" $ "c''") $ CNil)))}
        {t: CNil}
        {t: (CCons $ (CPLDeliver $ "n'" $ "m'") $ CNil)}.
      do 2 d_splitp. d_rotate 3. d_splitp. d_swap. d_substp.
      eapply DSCut; first by eapply DAPInNil.
      d_forallp {t: CPair $ 0 $ (CSLSend $ "n" $ (CPair $ "c'" $ "m"))}.
      eapply DSCut; first by eapply DSNotImpliesFalse with (Ac := {A:
                                                                     CPair $ 0 $ (CSLSend $ "n" $ (CPair $ "c'" $ "m")) \in CNil}).
      d_swap; eapply DARewriteIffPL; first by d_head.
      rewrite_assertion_any; d_swap; d_clear.
      d_ifp. d_head. d_false.

      (* prove for periodic *)
      d_ifp. d_ifc. d_splitp. d_swap. d_eval.
      d_destructtuplep
        {t: "Fs'" $ "Fn"} {t: "Fors"} {t: "Fois"}
        {t: "Fs" $ "Fn"}
        {t: CNil}
        {t: CNil}; do 2 d_splitp. d_ifc. d_splitp. d_swap.
      d_subst.
      eapply DSCut; first by eapply DAPInNil.
      d_forallp {t: CPair $ 0 $ (CSLSend $ "n" $ (CPair $ "c'" $ "m"))}.
      eapply DSCut; first by eapply DSNotImpliesFalse with (Ac := {A:
                                                                     CPair $ 0 $ (CSLSend $ "n" $ (CPair $ "c'" $ "m")) \in CNil}).
      d_swap; eapply DARewriteIffPL; first by d_head.
      rewrite_assertion_any; d_swap; d_clear.
      d_ifp. d_head. d_false.

      d_splitp. d_swap; d_clear.
      eapply DTGeneralization; first by repeat constructor.
      d_ifc. d_splitp. d_rotate 2. d_ifp. d_rotate 6. d_head.
      d_ifp. d_rotate 5. d_head.
      d_head.
    }

    (* by lemma 86 and lemma 96 *)
    d_have {A:
              ("Fn" = "n" /\ "Fd" = CCons $ 0 $ CNil /\ "Fo" = OIndication /\ "Fe" = CSLDeliver $ "n'" $ (CPair $ "c'" $ "m")) =>>
                                                                                                                               eventuallyp (on "n'", event []-> CPLSend $ "n" $ "m" /\ FLeft $ ("Fs'" $ "n") = "c'")
           }.
    {
      eapply DSCut; first by eapply DTL96_2 with (A1 := {A:
                                                           ("Fn" = "n" /\ "Fd" = CCons $ 0 $ CNil /\ "Fo" = OIndication /\ "Fe" = CSLDeliver $ "n'" $ (CPair $ "c'" $ "m"))})
                                                 (A2 := {A:
                                                           ("Fn" = "n'" /\ "Fd" = CCons $ 0 $ CNil /\ "Fo" = ORequest /\ "Fe" = CSLSend $ "n" $ (CPair $ "c'" $ "m"))})
                                                 (A3 := {A:
                                                           (eventuallyp (on "n'", (CPair $ 0 $ (CSLSend $ "n" $ (CPair $ "c'" $ "m")) \in "Fors") /\ self-event))}).
      d_ifp. d_splitc. d_rotate 2. d_head.
      d_swap. d_head.
      eapply DARewriteCongruentPR; first by apply DTL83_1 with (A := {A: (on "n'", (CPair $ 0 $ (CSLSend $ "n" $ (CPair $ "c'" $ "m")) \in "Fors") /\ self-event)}).
      rewrite_assertion_any.

      eapply DSCut; first by eapply DTL96_2 with (A1 := {A:
                                                           ("Fn" = "n" /\ "Fd" = CCons $ 0 $ CNil /\ "Fo" = OIndication /\ "Fe" = CSLDeliver $ "n'" $ (CPair $ "c'" $ "m"))})
                                                 (A2 := {A:
                                                           on "n'", (CPair $ 0 $ (CSLSend $ "n" $ (CPair $ "c'" $ "m")) \in "Fors") /\ self-event})
                                                 (A3 := {A:
                                                           on "n'", event []-> CPLSend $ "n" $ "m" /\ FLeft $ ("Fs'" $ "n") = "c'"}).
      d_ifp. d_splitc. d_head.
      d_swap. d_head.
      d_head.
    }
    d_head.
  }

  (* by rule SInv on (4) *)
  d_have {A:
            self (
                ("Fn" = "n" /\ "Fd" = CCons $ 0 $ CNil /\ "Fo" = OIndication /\ "Fe" = CSLDeliver $ "n'" $ (CPair $ "c'" $ "m")) =>> eventuallyp (on "n'", event []-> CPLSend $ "n" $ "m" /\ FLeft $ ("Fs'" $ "n") = "c'")
              )
         }.
  {
    d_have {A:
              ("Fn" = "n" /\ "Fd" = CCons $ 0 $ CNil /\ "Fo" = OIndication /\ "Fe" = CSLDeliver $ "n'" $ (CPair $ "c'" $ "m") <~
                                                                                                ("Fn" = "n'" /\ "Fd" = CNil /\ "Fo" = ORequest /\ "Fe" = CPLSend $ "n" $ "m") /\ FLeft $ ("Fs'" $ "n") = "c'") -> self ("Fn" = "n" /\ "Fd" = CCons $ 0 $ CNil /\ "Fo" = OIndication /\ "Fe" = CSLDeliver $ "n'" $ (CPair $ "c'" $ "m") <~
                                                                                                                                                                                                                                                                                                         ("Fn" = "n'" /\ "Fd" = CNil /\ "Fo" = ORequest /\ "Fe" = CPLSend $ "n" $ "m") /\ FLeft $ ("Fs'" $ "n") = "c'")
           }.
    {
      eapply DTL129.
    }
    d_ifp. d_head. d_head.
  }

  (* final steps *)
  d_have {A:
            eventuallyp (on "n'", event []-> CPLSend $ "n" $ "m" /\ FLeft $ ("Fs'" $ "n") = "c") /\ eventuallyp (on "n'", event []-> CPLSend $ "n" $ "m" /\ FLeft $ ("Fs'" $ "n") = "c'") =>> ("c" = "c'")
         }.
  {
    set B1 := {A: (on "n'", event []-> CPLSend $ "n" $ "m")}.
    set C1 := {A: FLeft $ ("Fs'" $ "n") = "c"}.
    set C2 := {A: FLeft $ ("Fs'" $ "n") = "c'"}.
    d_have {A:
              eventuallyp (B1 /\ C1) /\ eventuallyp (B1 /\ C2) =>>
                                            eventuallyp ((B1 /\ C1) /\ eventuallyp (B1 /\ C2)) \/
                                eventuallyp ((B1 /\ C2) /\ eventuallyp (B1 /\ C1))
           }.
    {
      eapply DSCut; first by eapply DTL102_2 with (A1 := {A: (on "n'", event []-> CPLSend $ "n" $ "m" /\ FLeft $ ("Fs'" $ "n") = "c")})
                                                  (A2 := {A: (on "n'", event []-> CPLSend $ "n" $ "m" /\ FLeft $ ("Fs'" $ "n") = "c'")}).
      d_head.
    }
    set P2 := {A: eventuallyp ((B1 /\ C2) /\ eventuallyp (B1 /\ C1))}.
    set P1 := {A:  eventuallyp ((B1 /\ C1) /\ eventuallyp (B1 /\ C2))}.

    d_have {A:
              eventuallyp ((B1 /\ C1)) /\ eventuallyp (B1 /\ C2) =>>
                          eventuallyp (B1 /\ C1 /\ eventuallyp C2) \/
              eventuallyp (B1 /\ C2 /\ eventuallyp C1)
           }.
    {
      d_have {A:
                B1 /\ C1 -> (alwaysp^ (~ B1)) /\ C1
             }.
      {
        d_ifc.
        eapply DARewriteEntailsP with (Arp := {A: B1})
                                      (Arc := {A: alwaysp^ (~ B1)}).
        d_rotate 8. d_head. rewrite_assertion_pos.
        d_head.
      }

      d_have {A:
                P1 -> ((eventuallyp (((alwaysp^ (~ B1)) /\ C1) /\ eventuallyp (B1 /\ C2))))}.
      {
        d_ifc.
        eapply DARewriteIfP; first by d_head. rewrite_assertion_pos.
        d_head.
      }
      d_swap; d_clear.
      d_swap.

      eapply DARewriteIfP; first by d_head. rewrite_assertion_pos.
      d_swap. d_clear.
      set P1' := {A: ((eventuallyp (((alwaysp^ (~ B1)) /\ C1) /\ eventuallyp (B1 /\ C2))))}.
      set P2' := {A: eventuallyp ((B1 /\ C2) /\ eventuallyp (B1 /\ C1))}.

      d_have {A:
                eventuallyp (B1 /\ C2) -> (eventuallyp B1) /\ (eventuallyp C2)}.
      {
        d_ifc.
        eapply DARewriteEntailsP; first by apply DTL127_5 with (A := B1)
                                                               (B := C2).
        rewrite_assertion_pos. d_head.
      }
      d_swap. eapply DARewriteIfP; first by d_head. rewrite_assertion_pos.
      set P1'' := {A: ((eventuallyp (((alwaysp^ (~ B1)) /\ C1) /\ (eventuallyp B1) /\ (eventuallyp C2))))}.
      set P2'' := {A: eventuallyp ((B1 /\ C2) /\ eventuallyp (B1 /\ C1))}.
      d_have {A:
                (((alwaysp^ (~ B1)) /\ C1) /\ (eventuallyp B1) /\ (eventuallyp C2))
                -> (((eventuallyp B1) /\ (alwaysp^ (~ B1))) /\ C1 /\ eventuallyp C2)
             }.
      {
        d_ifc.
        d_splitp. d_splitp. d_splitc. d_rotate 2. d_splitp. d_splitc. d_head.
        d_rotate 14.
        d_head. d_splitc. d_swap. d_head. d_rotate 2. d_splitp. d_swap. d_head.
      }
      d_swap. eapply DARewriteIfP; first by d_head. rewrite_assertion_pos.
      set F1 := {A: (((eventuallyp B1) /\ (alwaysp^ (~ B1))) /\ C1 /\ eventuallyp C2)}.
      set G1 := {A: eventuallyp ((B1 /\ C2) /\ eventuallyp (B1 /\ C1))}.

      d_have {A:
                (((eventuallyp B1) /\ (alwaysp^ (~ B1))) /\ C1 /\ eventuallyp C2)
                  -> B1 /\ C1 /\ eventuallyp C2
             }.
      {
        d_ifc.
        eapply DARewriteEntailsP; first by apply DTL103_2 with (A := B1).
        rewrite_assertion_pos.
        d_head.
      }
      d_swap. eapply DARewriteIfP; first by d_head. rewrite_assertion_pos.
      set F2 := {A: eventuallyp (B1 /\ C1 /\ eventuallyp C2)}.
      set G2 := {A: (eventuallyp ((B1 /\ C2) /\ eventuallyp (B1 /\ C1)))}.

      d_have {A:
                (eventuallyp ((B1 /\ C2) /\ eventuallyp (B1 /\ C1)))
                -> eventuallyp (B1 /\ C2 /\ eventuallyp C1)
             }.
      {
        d_ifc.
        d_have {A:
                  B1 /\ C2 -> (alwaysp^ (~ B1)) /\ C2
               }.
        {
          d_ifc.
          eapply DARewriteEntailsP with (Arp := {A: B1})
                                        (Arc := {A: alwaysp^ (~ B1)}).
          d_rotate 12. d_head. rewrite_assertion_pos.
          d_head.
        }

        d_have {A:
                  P2 -> ((eventuallyp (((alwaysp^ (~ B1)) /\ C2) /\ eventuallyp (B1 /\ C1))))}.
        {
          d_ifc.
          eapply DARewriteIfP; first by d_head. rewrite_assertion_pos.
          d_head.
        }
        d_swap; d_clear.
        d_swap.

        eapply DARewriteIfP; first by d_head. rewrite_assertion_pos.
        d_swap. d_clear.
        d_have {A:
                  eventuallyp (B1 /\ C1) -> (eventuallyp B1) /\ (eventuallyp C1)}.
        {
          d_ifc.
          eapply DARewriteEntailsP; first by apply DTL127_5 with (A := B1)
                                                                 (B := C1).
          rewrite_assertion_pos. d_head.
        }
        d_swap. eapply DARewriteIfP; first by d_head. rewrite_assertion_pos.

        d_have {A:
                  (((alwaysp^ (~ B1)) /\ C2) /\ (eventuallyp B1) /\ (eventuallyp C1))
                  -> (((eventuallyp B1) /\ (alwaysp^ (~ B1))) /\ C2 /\ eventuallyp C1)
               }.
        {
          d_ifc.
          d_splitp. d_splitp. d_splitc. d_rotate 2. d_splitp. d_splitc. d_head.
          d_rotate 18.
          d_head. d_splitc. d_swap. d_head. d_rotate 2. d_splitp. d_swap. d_head.
        }
        d_swap. eapply DARewriteIfP; first by d_head. rewrite_assertion_pos.
        d_have {A:
                  (((eventuallyp B1) /\ (alwaysp^ (~ B1))) /\ C2 /\ eventuallyp C1)
                  -> B1 /\ C2 /\ eventuallyp C1
               }.
        {
          d_ifc.
          eapply DARewriteEntailsP; first by apply DTL103_2 with (A := B1).
          rewrite_assertion_pos.
          d_head.
        }
        d_swap. eapply DARewriteIfP; first by d_head. rewrite_assertion_pos.
        d_head.
      }
      d_have {A:
                F2 \/ (eventuallyp ((B1 /\ C2) /\ eventuallyp (B1 /\ C1)))
                -> F2 \/ eventuallyp (B1 /\ C2 /\ eventuallyp C1)
             }.
      {
        d_ifc. d_orp. d_left. d_head.
        d_right.
        eapply DARewriteIfP; first by d_head. rewrite_assertion_pos.
        d_head.
      }
      d_swap; d_clear.
      d_swap. eapply DARewriteIfP; first by d_head. rewrite_assertion_pos.

      d_head.
    }

    set E := {A:
                (eventuallyp (B1 /\ C1 /\ eventuallyp C2) \/
                 eventuallyp (B1 /\ C2 /\ eventuallyp C1))}.

    d_have {A:
              (eventuallyp (B1 /\ C1 /\ eventuallyp C2) \/
               eventuallyp (B1 /\ C2 /\ eventuallyp C1)) ->
              eventuallyp (C1 /\ C2)
           }.
    {
      d_subst.
      set E1 := {A:
                (eventuallyp (B1 /\ C1 /\ eventuallyp C2) \/
                 eventuallyp (B1 /\ C2 /\ eventuallyp C1))}.
      d_ifc.
      set D1 := {A: ((B1 /\ C1 /\ eventuallyp C2))}.
      set D2 := {A: ((B1 /\ C2 /\ eventuallyp C1))}.
      d_have {A:
                D1 -> (C1 /\ C2)}.
      {
        d_ifc. d_splitp. d_swap. d_splitp. d_splitc. d_head. d_swap.
        d_subst.
        eapply DSCut; first by eapply DTL133 with (P := {A: "c" = "c'"}).
        d_ifp. d_head.
        d_head.
      }
      d_swap. eapply DARewriteIfP; first by d_head. rewrite_assertion_pos.
      set E2 := {A:
                (eventuallyp (C1 /\ C2) \/
                 (eventuallyp (B1 /\ C2 /\ eventuallyp C1)))}.
      d_have {A:
                D2 -> (C1 /\ C2)}.
      {
        d_ifc. d_splitp. d_swap. d_splitp. d_swap. d_splitc.
        d_subst.
        eapply DSCut; first by eapply DTL133 with (P := {A: "c'" = "c"}).
        d_ifp. d_head. d_head.
        d_swap. d_head.
      }
      d_swap. eapply DARewriteIfP; first by d_head. rewrite_assertion_pos.
      set E3 := {A:
                   (eventuallyp (C1 /\ C2) \/
                    eventuallyp (C1 /\ C2))}.

      set E4 := {A: eventuallyp (C1 /\ C2) \/ eventuallyp (C1 /\ C2)}.
      d_have {A:
                E4 -> eventuallyp (C1 /\ C2)}.
      {
        d_ifc. d_orp. d_head. d_head.
      }
      d_swap. eapply DARewriteIfP; first by d_head. rewrite_assertion_pos.
      d_head.
    }
    set E5 := {A:
                 (eventuallyp (B1 /\ C1 /\ eventuallyp C2) \/
                  eventuallyp (B1 /\ C2 /\ eventuallyp C1))}.
    d_swap. eapply DARewriteIfP; first by d_head. rewrite_assertion_pos.

    d_have {A:
              C1 /\ C2 -> "c" = "c'"}.
    {
      d_ifc. d_splitp. d_substp.
      eapply DSCut; first by apply DAPEqualSymmetric. d_forallp "c". d_forallp "c'".
      d_splitp. d_clear. d_ifp. d_head. d_head.
    }
    d_swap. eapply DARewriteIfP; first by d_head. rewrite_assertion_pos.
    d_have {A:
              eventuallyp ("c" = "c'") -> "c" = "c'"}.
    {
      eapply DSCut; first by eapply DTL133 with (P := {A: "c" = "c'"}).
      d_head.
    }
    d_swap. eapply DARewriteIfP; first by d_head. rewrite_assertion_pos.
    d_head.
  }
  set A1 := {A: "Fn" = "n" /\ "Fd" = CCons $ 0 $ CNil /\ "Fo" = OIndication /\ "Fe" = CSLDeliver $ "n'" $ (CPair $ "c" $ "m")}.
  set A2 := {A: "Fn" = "n" /\ "Fd" = CCons $ 0 $ CNil /\ "Fo" = OIndication /\ "Fe" = CSLDeliver $ "n'" $ (CPair $ "c'" $ "m")}.
  set B1 := {A: on "n'", event []-> CPLSend $ "n" $ "m" /\ FLeft $ ("Fs'" $ "n") = "c"}.
  set B2 := {A: on "n'", event []-> CPLSend $ "n" $ "m" /\ FLeft $ ("Fs'" $ "n") = "c'"}.


  d_have {A:
            eventuallyp A2 =>> eventuallyp eventuallyp A2}.
  {
    eapply DSCut; first by apply DTL83_1 with (A := {A: A2}).
    d_splitp. d_head.
  }
  eapply DARewriteEntailsP with (Arp := {A: A2})
                                (Arc := {A: eventuallyp B2}).
  d_rotate 2. d_head. rewrite_assertion_pos.
  eapply DARewriteCongruentPR; first by apply DTL83_1 with (A := {A: B2}).
  rewrite_assertion_any.
  eapply DARewriteCongruentPR; first by apply DTL83_1 with (A := {A: B2}).
  rewrite_assertion_any.

  eapply DSCut; first by apply DTL132 with (A1 := {A: A1})
                                           (A2 := {A: eventuallyp A2})
                                           (B1 := {A: eventuallyp B1})
                                           (B2 := {A: eventuallyp B2}).
  d_ifp. d_splitc. d_rotate 5. d_head. d_head.
  d_swap; d_clear.
  eapply DARewriteEntailsP; first by d_head.
  rewrite_assertion_pos.
  d_have {A:
            (A1 /\ eventuallyp A2 =>> "c" = "c'") ->
            self (A1 /\ eventuallyp A2 =>> "c" = "c'")
         }.
  {
    eapply DTL129.
  }
  d_swap. eapply DARewriteIfP; first by d_head.
  rewrite_assertion_pos.
  d_head.
Qed.

(* No-duplication
 * If a message is sent at most once, it will be delivered at most once.
 *)
Theorem PL_2 : Context [:: V "c"; V "m"; V "n'"; V "n"] [::] |- perfect_link, {A:
  (on "n'", event []-> CPLSend $ "n" $ "m" =>>
    alwaysp^ ~on "n'", event []-> CPLSend $ "n" $ "m") ->
  (on "n", event []<- CPLDeliver $ "n'" $ "m" =>>
    alwaysp^ ~on "n", event []<- CPLDeliver $ "n'" $ "m")
}.
Proof.
  d_ifc.
  (* by OI' *)
  d_have {A:
            on "n", event[]<- CPLDeliver $ "n'" $ "m" =>>
                         eventuallyp (self-event /\ on "n", (CPLDeliver $ "n'" $ "m" \in "Fois"))
         }.
  {
    d_use DPOI'. d_forallp "n". d_forallp {t: CPLDeliver $ "n'" $ "m"}.
      by eapply DARewriteIfP; first by apply DTL123 with (A := {A:
                                                                  self-event /\ on "n", (CPLDeliver $ "n'" $ "m" \in "Fois")}).
  }

  (* by INVL *)
  d_have {A:
            self-event /\ "Fn" = "n" /\ (CPLDeliver $ "n'" $ "m" \in "Fois") =>>
            self-event /\ "Fn" = "n" /\ ((FOcc $ "Fois" $ (CPLDeliver $ "n'" $ "m")) = 1)
         }.
  {
    eapply DSCut; first by apply DPInvL with (A := {A:
          "Fn" = "n" /\ (CPLDeliver $ "n'" $ "m" \in "Fois") ->
          "Fn" = "n" /\ ((FOcc $ "Fois" $ (CPLDeliver $ "n'" $ "m")) = 1)});
    first by repeat constructor.

    (* request *)
    d_ifp. d_forallc "e".
    d_ifc. d_splitp. d_swap. d_evalp.
    d_destructp (fun t => {A: ("Fs'" $ "Fn", "Fors", "Fois") = t}).
    d_forallp "r"; d_forallp "c"; d_splitp; d_swap.
    d_substp; d_evalp.
    d_destructp (fun t => {A: ("Fs'" $ "Fn", "Fors", "Fois") = t}).
    d_forallp "m". d_forallp "n'".
    d_splitp. d_swap.
    d_substp. d_evalp.
    d_ifc. d_swap.
    d_destructtuplep
      {t: "Fs'" $ "Fn"} {t: "Fors"} {t: "Fois"}
      {t: (FSucc $ "c", "r")}
      {t: (CCons $ (CPair $ 0 $ (CSLSend $ "n'" $ (CPair $ (FSucc $ "c") $ "m"))) $ CNil)} {t: CNil}; do 2 d_splitp.
    d_rotate 3. d_substp.
    d_splitp. d_swap.

    eapply DSCut; first by eapply DAPInNil.
    d_forallp {t: (CPLDeliver $ "n'" $ "m")}.
    eapply DSCut; first by eapply DSNotImpliesFalse with (Ac := {A: (CPLDeliver $ "n'" $ "m") \in CNil}).
    d_swap; eapply DARewriteIffPL; first by d_head.
    rewrite_assertion_any; d_swap; d_clear.
    d_ifp. d_head. d_false.

    (* indication *)
    d_ifp. d_forallc "i". d_forallc "e".
    d_ifc. d_splitp. d_swap. d_evalp.
    d_destructp (fun t => {A: ("Fs'" $ "Fn", "Fors", "Fois") = t}).
    d_forallp "r"; d_forallp "c"; d_splitp; d_swap.
    d_substp; d_evalp.
    d_destructp (fun t => {A: ("Fs'" $ "Fn", "Fors", "Fois") = t}).
    d_forallp "m"; d_forallp "c'"; d_forallp "n'". (* n' or n? *)
    d_splitp. d_swap. d_substp. d_evalp.
    d_destructp (fun t => {A: ("Fs'" $ "Fn", "Fors", "Fois") = t}).

    d_orp.
    (* true case *)
    d_splitp. d_swap. d_substp. d_evalp.
    d_destructtuplep
        {t: "Fs'" $ "Fn"} {t: "Fors"} {t: "Fois"}
        {t: ("c", "r")}
        {t:  CNil} {t: CNil}; do 2 d_splitp.
    d_ifc. d_substp. d_splitp. d_swap.
    eapply DSCut; first by eapply DAPInNil.
    d_forallp {t: (CPLDeliver $ "n'" $ "m")}.
    eapply DSCut; first by eapply DSNotImpliesFalse with (Ac := {A: (CPLDeliver $ "n'" $ "m") \in CNil}).
    d_swap; eapply DARewriteIffPL; first by d_head.
    rewrite_assertion_any; d_swap; d_clear.
    d_ifp. d_head. d_false.

    (* false case *)
    d_splitp. d_swap. d_substp. d_evalp.
    d_destructtuplep
      {t: "Fs'" $ "Fn"} {t: "Fors"} {t: "Fois"}
      {t: (CPair $ "c" $ (FUnion $ "r" $ (CCons $ (CPair $ "n'" $ "c'") $ CNil)))}
      {t:  CNil} {t: (CCons $ (CPLDeliver $ "n'" $ "m") $ CNil)}. do 2 d_splitp.
    d_ifc.
    d_splitc. d_splitp. d_head.
    d_subst. d_eval.
    eapply DAPListOcc. by []. by [].

    (* periodics *)
    d_ifp. d_ifc. d_splitp. d_swap. d_evalp.
    d_destructtuplep
      {t: "Fs'" $ "Fn"} {t: "Fors"} {t: "Fois"}
      {t: "Fs" $ "Fn"}
      {t:  CNil} {t: CNil}; do 2 d_splitp.
    d_ifc. d_splitp. d_splitc. d_head.
    d_swap. d_substp.
    eapply DSCut; first by eapply DAPInNil.
    d_forallp {t: (CPLDeliver $ "n'" $ "m")}.
    eapply DSCut; first by eapply DSNotImpliesFalse with (Ac := {A: (CPLDeliver $ "n'" $ "m") \in CNil}).
    d_swap; eapply DARewriteIffPL; first by d_head.
    rewrite_assertion_any; d_swap; d_clear.
    d_ifp. d_head. d_false.

    eapply DARewriteIffPL; first by apply DSMergeIf with
      (Ap1 := {A: self-event})
      (Ap2 := {A: "Fn" = "n" /\ CPLDeliver $ "n'" $ "m" \in "Fois"})
      (Ac := {A: "Fn" = "n" /\ (fun: fun: FCount $ (P 0 0) $ (P 1 0)) $ "Fois" $ (CPLDeliver $ "n'" $ "m") = 1}).
    rewrite_assertion_any.

    d_have {A:
              (self-event /\ "Fn" = "n" /\ CPLDeliver $ "n'" $ "m" \in "Fois" =>> self-event /\ "Fn" = "n" /\ (fun: fun: FCount $ (P 0 0) $ (P 1 0)) $ "Fois" $ (CPLDeliver $ "n'" $ "m") = 1)}.
    {
      eapply DTGeneralization; first by repeat constructor.
      d_ifc. d_swap. d_splitp. d_swap; d_clear.
      d_ifp. d_head.
      d_splitc. d_swap. d_splitp. d_head. d_head.
    }
    d_head.
  }

  (* by Lemma 96 on (1) and (2) *)
  d_have {A:
            on "n", event []<- CPLDeliver $ "n'" $ "m" =>>
                          eventuallyp (self-event /\ on "n", ((FOcc $ "Fois" $ (CPLDeliver $ "n'" $ "m")) = 1))}.
  {
    d_rotate 2. d_clear. d_swap.
    eapply DSCut; first by apply DTL96_2 with
                             (A1 := {A: on "n", event []<- CPLDeliver $ "n'" $ "m"})
                             (A2 := {A: self-event /\ on "n", (CPLDeliver $ "n'" $ "m" \in "Fois")})
                             (A3 := {A: self-event /\ "Fn" = "n" /\ (fun: fun: FCount $ (P 0 0) $ (P 1 0)) $ "Fois" $ (CPLDeliver $ "n'" $ "m") = 1}).
    d_ifp. d_splitc. d_head. d_swap. d_head.
    d_head.
  }

  (* by Lemma 42 *)
  d_have {A:
            self (
                "Fn" = "n" /\ (CPLDeliver $ "n'" $ "m") \in "Fois" =>>
                                                                   always^ ("Fn" = "n" -> (CPLDeliver $ "n'" $ "m") \notin "Fois") /\
                                                            alwaysp^ ("Fn" = "n" -> (CPLDeliver $ "n'" $ "m") \notin "Fois")
         )}.
  {
    do 4 d_clear.
    eapply L42.
  }

  (* by SINV on (4) *)
  d_have {A:
            self-event /\ "Fn" = "n" /\ CPLDeliver $ "n'" $ "m" \in "Fois" =>>
                                                                           always^ (self-event /\ "Fn" = "n" -> (CPLDeliver $ "n'" $ "m") \notin "Fois") /\
                                                                    alwaysp^ (self-event /\ "Fn" = "n" -> (CPLDeliver $ "n'" $ "m") \notin "Fois")}.
  {
    eapply DARewriteIfP with (Arp := {A:
                                          (self ("Fn" = "n" /\ CPLDeliver $ "n'" $ "m" \in "Fois" =>>                                                                                          always^ ("Fn" = "n" -> CPLDeliver $ "n'" $ "m" \notin "Fois") /\ alwaysp^ ("Fn" = "n" -> CPLDeliver $ "n'" $ "m" \notin "Fois")))})
                               (Arc := {A: restrict_assertion {A: self-event} ( (("Fn" = "n" /\ CPLDeliver $ "n'" $ "m" \in "Fois") =>>  (always^ ("Fn" = "n" -> CPLDeliver $ "n'" $ "m" \notin "Fois") /\ alwaysp^ ("Fn" = "n" -> CPLDeliver $ "n'" $ "m" \notin "Fois"))))}).

    eapply DPSInv_1.
    rewrite_assertion_pos.
    d_splitp.
    d_swap.
    set A := {A: (self-event -> "Fn" = "n" /\ CPLDeliver $ "n'" $ "m" \in "Fois")}.
    set B := {A: always^ (self-event -> "Fn" = "n" -> CPLDeliver $ "n'" $ "m" \notin "Fois") /\
                 alwaysp^ (self-event -> "Fn" = "n" -> CPLDeliver $ "n'" $ "m" \notin "Fois")}.
    d_have {A:
              always^ (self-event -> "Fn" = "n" /\ CPLDeliver $ "n'" $ "m" \in "Fois" -> B) -> always ((self-event /\ "Fn" = "n" /\ CPLDeliver $ "n'" $ "m" \in "Fois") -> B)}.
    {
      d_ifc. d_splitc. d_ifc. d_rotate 3. d_ifp. d_rotate 4. d_splitp. d_swap. d_head. d_head.
      d_have {A:
              (self-event -> "Fn" = "n" /\ CPLDeliver $ "n'" $ "m" \in "Fois" -> B) ->
              ((self-event /\ "Fn" = "n" /\ CPLDeliver $ "n'" $ "m" \in "Fois") -> B)
             }.
      {
        d_ifc. d_ifc. d_splitp. d_rotate 2. d_ifp. d_rotate 7. d_head. d_ifp. d_rotate 8. d_head. d_head.

      }

      d_swap. eapply DARewriteIfP; first by d_head. rewrite_assertion_pos. d_head.
    }
    d_swap.
    eapply DARewriteIfP; first by d_head.
    rewrite_assertion_pos.
    d_have {A:
              (self-event -> "Fn" = "n" -> CPLDeliver $ "n'" $ "m" \notin "Fois") ->
              ((self-event /\ "Fn" = "n" -> CPLDeliver $ "n'" $ "m" \notin "Fois"))
           }.
    {
      d_ifc. d_ifc. d_splitp. d_rotate 2. d_ifp. d_rotate 7. d_head. d_ifp. d_rotate 8. d_head. d_head.
    }
    d_swap. eapply DARewriteIfP; first by d_head. rewrite_assertion_pos.
    d_head.
  }

  (* from (3) and (5) *)
  d_have {A:
            on "n", event []<- CPLDeliver $ "n'" $ "m" =>>
                          eventuallyp (((FOcc $ "Fois" $ (CPLDeliver $ "n'" $ "m")) = 1) /\
                                      always^ (self-event /\ "Fn" = "n" -> (CPLDeliver $ "n'" $ "m") \notin "Fois") /\ alwaysp^ (self-event /\ "Fn" = "n" -> (CPLDeliver $ "n'" $ "m") \notin "Fois"))
         }.
  {
    d_have {A: ((FOcc $ "Fois" $ (CPLDeliver $ "n'" $ "m")) = 1) -> CPLDeliver $ "n'" $ "m" \in "Fois"}.
    {
      d_ifc.
      d_eval.
      eapply DSCut; first by eapply DAPEqualToGE.
      d_forallp {t: FCount $ (CPLDeliver $ "n'" $ "m") $ "Fois"}.
      d_forallp 1. d_ifp.
      d_head.
      d_use DAPInOcc.
      d_evalp. d_forallp {t: (CPLDeliver $ "n'" $ "m")}. d_forallp "Fois". d_splitp.
      d_clear. d_ifp. d_head.
      d_head.
    }

    d_have {A: self-event /\ "Fn" = "n" /\ ((FOcc $ "Fois" $ (CPLDeliver $ "n'" $ "m")) = 1)
               ->
               ((FOcc $ "Fois" $ (CPLDeliver $ "n'" $ "m")) = 1) /\ (self-event /\ "Fn" = "n" /\ CPLDeliver $ "n'" $ "m" \in "Fois")}.
    {
      d_ifc.
      d_splitc. do 2 (d_splitp; d_swap). d_head.
      eapply DARewriteIfP with (Arp := {A: (fun: fun: FCount $ (P 0 0) $ (P 1 0)) $ "Fois" $ (CPLDeliver $ "n'" $ "m") = 1})
                               (Arc := {A: CPLDeliver $ "n'" $ "m" \in "Fois"}).
      d_head. rewrite_assertion_pos. d_head.
    }
    eapply DARewriteEntailsP with (Arp := {A: self-event /\ "Fn" = "n" /\ CPLDeliver $ "n'" $ "m" \in "Fois"})
                                  (Arc := {A:  always^ (self-event /\ "Fn" = "n" -> CPLDeliver $ "n'" $ "m" \notin "Fois") /\
                        alwaysp^ (self-event /\ "Fn" = "n" -> CPLDeliver $ "n'" $ "m" \notin "Fois")}).
    d_swap. d_head. rewrite_assertion_pos.
    d_rotate 4.
    eapply DARewriteIfP with (Arp := {A: self-event /\ "Fn" = "n" /\ (fun: fun: FCount $ (P 0 0) $ (P 1 0)) $ "Fois" $ (CPLDeliver $ "n'" $ "m") = 1})
                             (Arc := {A:  (fun: fun: FCount $ (P 0 0) $ (P 1 0)) $ "Fois" $ (CPLDeliver $ "n'" $ "m") = 1 /\
                        always^ (self-event /\ "Fn" = "n" -> CPLDeliver $ "n'" $ "m" \notin "Fois") /\
                        alwaysp^ (self-event /\ "Fn" = "n" -> CPLDeliver $ "n'" $ "m" \notin "Fois")}).
    d_rotate 3. d_head. rewrite_assertion_pos. d_head.
  }

  (* by UNIOI *)
  d_have {A:
            (((FOcc $ "Fois" $ (CPLDeliver $ "n'" $ "m")) <= 1) /\
             always^ (self-event /\ "Fn" = "n" -> (CPLDeliver $ "n'" $ "m") \notin "Fois") /\
             alwaysp^ (self-event /\ "Fn" = "n" -> (CPLDeliver $ "n'" $ "m") \notin "Fois")) =>>
                                                                                             on "n", event[]<- CPLDeliver $ "n'" $ "m" =>>
                                                                                                          alwaysp^ (~ (on "n", event[]<- CPLDeliver $ "n'" $ "m"))
         }.
  {
    d_use DPUniOI.
    d_forallp "n". d_forallp "Fois". d_forallp {t: CPLDeliver $ "n'" $ "m"}.
    set A := {A: always^ (self-event /\ "Fn" = "n" -> (CPLDeliver $ "n'" $ "m") \notin "Fois")}.
    set B := {A: alwaysp^ (self-event /\ "Fn" = "n" -> (CPLDeliver $ "n'" $ "m") \notin "Fois")}.
    set D := {A:  (fun: fun: FCount $ (P 0 0) $ (P 1 0)) $ "Fois" $ (CPLDeliver $ "n'" $ "m") <= 1}.
    set E := {A: alwaysp^ (~ ("Fn" = "n" /\ "Fd" = CNil /\ "Fo" = OIndication /\ "Fe" = CPLDeliver $ "n'" $ "m"))}.
    set F := {A: always^ (~ ("Fn" = "n" /\ "Fd" = CNil /\ "Fo" = OIndication /\ "Fe" = CPLDeliver $ "n'" $ "m"))}.
    eapply DARewriteIfP with (Arp := {A: E /\ F})
                             (Arc := {A: E}).
    d_ifc. d_splitp. d_head.
    rewrite_assertion_pos.
    d_head.
  }

  (* from (6) and (7) *)
  d_have {A:
            on "n", event []<- CPLDeliver $ "n'" $ "m" <~
                          (on "n", event []<- CPLDeliver $ "n'" $ "m" =>> alwaysp^ (~ on "n", event []<- CPLDeliver $ "n'" $ "m"))}.
  {
    d_swap.
    d_use DAPEqualToLe.
    d_forallp {t: (fun: fun: FCount $ (P 0 0) $ (P 1 0)) $ "Fois" $ (CPLDeliver $ "n'" $ "m")}. d_forallp 1.
    d_swap.
    eapply DARewriteIfP with (Arp := {A: (fun: fun: FCount $ (P 0 0) $ (P 1 0)) $ "Fois" $ (CPLDeliver $ "n'" $ "m") = 1})
                             (Arc := {A: (fun: fun: FCount $ (P 0 0) $ (P 1 0)) $ "Fois" $ (CPLDeliver $ "n'" $ "m") <= 1}).
    d_head. rewrite_assertion_pos.
    d_swap. d_clear.
    eapply DARewriteEntailsP with (Arp := {A: (fun: fun: FCount $ (P 0 0) $ (P 1 0)) $ "Fois" $ (CPLDeliver $ "n'" $ "m") <= 1 /\
                        always^ (self-event /\ "Fn" = "n" -> CPLDeliver $ "n'" $ "m" \notin "Fois") /\
                        alwaysp^ (self-event /\ "Fn" = "n" -> CPLDeliver $ "n'" $ "m" \notin "Fois")})
                                  (Arc := {A: on "n", event []<- CPLDeliver $ "n'" $ "m" =>> alwaysp^ (~ on "n", event []<- CPLDeliver $ "n'" $ "m")}).
    d_head. rewrite_assertion_pos.
    d_head.
  }

  d_have {A:
            on "n", event []<- CPLDeliver $ "n'" $ "m" =>>
                          alwaysp^ (~ (on "n", event []<- CPLDeliver $ "n'" $ "m"))}.
  {
    set A := {A:  on "n", event []<- CPLDeliver $ "n'" $ "m"}.

    eapply DARewriteEntailsP with (Arp := {A: eventuallyp always (A -> alwaysp^ (~A))})
                                  (Arc := {A: (A -> alwaysp^ (~A))}).
    eapply DTL98_1.
    rewrite_assertion_pos.
    d_subst.
    set B := {A: "Fn" = "n" /\ "Fd" = CNil /\ "Fo" = OIndication /\ "Fe" = CPLDeliver $ "n'" $ "m"}.
    d_have {A:
              (B -> (B -> alwaysp^ (~ B))) -> (B -> alwaysp^ (~ B))}.
    {
      d_ifc. d_ifc. d_swap. d_ifp. d_head. d_ifp. d_head. d_head.
    }
    d_swap. eapply DARewriteIfP with (Arp := {A: (B -> B -> alwaysp^ (~ B))})
                                     (Arc := {A:  B -> alwaysp^ (~ B)}).
    d_head.
    rewrite_assertion_pos.
    d_head.
  }
  d_head.
Qed.

(* No-forge
 * If a node n delivers a message m with sender n', then m was previously sent
 * to n by node n'.
 *)
Theorem PL_3 : Context [:: V "m"; V "n'"; V "n"] [::] |- perfect_link, {A:
  on "n", event []<- CPLDeliver $ "n'" $ "m" <~
  on "n'", event []-> CPLSend $ "n" $ "m"
}.
Proof.
  (* By OI' *)
  d_have {A:
    on "n", event []<- CPLDeliver $ "n'" $ "m" =>>
    eventuallyp^ (self-event /\ on "n",
      (CPLDeliver $ "n'" $ "m" \in "Fois"))
  }.
  {
    (* Instantiate OI' *)
    by d_use DPOI'; d_forallp "n"; d_forallp {t: CPLDeliver $ "n'" $ "m"}.
  }

  (* By InvL *)
  d_have {A:
    self-event /\ on "n", (CPLDeliver $ "n'" $ "m" \in "Fois") =>>
    exists: "c": on "n", event [0]<- CSLDeliver $ "n'" $ ("c", "m")
  }.
  {
    d_clear. (* Clean up the context *)

    (* Instantiate InvL *)
    eapply DSCut; first by apply DPInvL with
      (A := {A:
          on "n", (CPLDeliver $ "n'" $ "m" \in "Fois") ->
          exists: "c": on "n", event [0]<- CSLDeliver $ "n'" $ ("c", "m")
        }); first by repeat constructor.

    (* Prove for requests *)
    d_ifp.
    d_forallc "e".
    d_ifc; d_splitp; d_swap; d_evalp.
    d_destructp (fun t => {A: ("Fs'" $ "Fn", "Fors", "Fois") = t}).
    d_forallp {t: ("c", "m")}; d_forallp "n'"; d_splitp; d_swap.
    d_substp; d_evalp.
    d_destructp (fun t => {A: ("Fs'" $ "Fn", "Fors", "Fois") = t}).
    d_forallp {t: ("c", "m")}.
    d_forallp "n'"; d_splitp; d_swap.
    d_substp; d_evalp.
    d_ifc; d_swap.
    d_destructtuplep
      {t: "Fs'" $ "Fn"} {t: "Fors"} {t: "Fois"}
        {t: (FSucc $ "n'", ("c", "m"))}
        {t: (CCons $ (CPair $ 0 $ (CSLSend $ "n'" $ (CPair $ (FSucc $ "n'") $ (CPair $ "c" $ "m")))) $ CNil)} {t: CNil}; do 2 d_splitp.
    d_rotate 3; d_substp; d_splitp; d_swap.

    eapply DSCut; first by eapply DAPInNil.
    d_forallp {t: CPLDeliver $ "n'" $ "m"}.
    eapply DSCut; first by eapply DSNotImpliesFalse with (Ac := {A:
                                                                   CPLDeliver $ "n'" $ "m" \in CNil}).
    d_swap; eapply DARewriteIffPL; first by d_head.
    rewrite_assertion_any; d_swap; d_clear.
      by d_ifp; first by d_head; d_false.

    (* Prove for indications *)
      d_ifp.
      d_forallc "i"; d_forallc "e".
      d_ifc. d_splitp. d_swap. d_evalp.
      d_destructp (fun t => {A: ("Fs'" $ "Fn", "Fors", "Fois") = t}).
      d_forallp "m"; d_forallp "n'"; d_splitp; d_swap.
      d_substp; d_evalp.
      d_destructp (fun t => {A: ("Fs'" $ "Fn", "Fors", "Fois") = t}).
      d_forallp "m"; d_forallp "c"; d_forallp "n'".
      d_splitp; d_swap.
      d_substp; d_evalp.
      d_destructp (fun t => {A: ("Fs'" $ "Fn", "Fors", "Fois") = t}).

      d_orp.
      (* true case *)
      d_splitp; d_swap. d_substp. d_evalp.
      d_destructtuplep
        {t: "Fs'" $ "Fn"} {t: "Fors"} {t: "Fois"}
        {t: ("n'", "m")}
        {t:  CNil} {t: CNil}; do 2 d_splitp.
      d_ifc. d_substp; d_splitp; d_swap.
      eapply DSCut; first by eapply DAPInNil.
      d_forallp {t: CPLDeliver $ "n'" $ "m"}.
      eapply DSCut; first by eapply DSNotImpliesFalse with (Ac := {A:
                                                                     CPLDeliver $ "n'" $ "m" \in CNil}).
      d_swap; eapply DARewriteIffPL; first by d_head.
      rewrite_assertion_any; d_swap; d_clear.
        by d_ifp; first by d_head; d_false.

      (* false case *)
      d_splitp; d_swap. d_substp. d_evalp.
      d_destructtuplep
        {t: "Fs'" $ "Fn"} {t: "Fors"} {t: "Fois"}
        {t: ("n'", (FUnion $ "m" $ (CCons $ (CPair $ "n'" $ "c") $ CNil)))}
        {t:  CNil} {t: (CCons $ (CPLDeliver $ "n'" $ "m") $ CNil)}; do 2 d_splitp.

      d_ifc. d_splitp.
      d_existsc "c".
      d_rotate 6.
      d_destructpairp {t: "i"} {t: "e"} {t: 0} {t: (CSLDeliver $ "n'" $ (CPair $ "c" $ "m"))}.
      rewrite_assertion_any; d_splitp.

      d_splitc. d_rotate 4. d_head.
      d_splitc. d_rotate 3. d_substp. d_splitp. d_head.
      d_rotate 3. do 2 (d_splitp; d_swap). d_swap. d_splitc. d_head.
      d_swap. d_substp. d_head.

    (* Prove for periodics *)
    d_ifp.
    d_ifc. d_splitp. d_swap. d_evalp.
    d_destructtuplep
      {t: "Fs'" $ "Fn"} {t: "Fors"} {t: "Fois"}
      {t: "Fs" $ "Fn"}
      {t:  CNil} {t: CNil}; do 2 d_splitp.
    d_ifc. d_substp. d_splitp; d_swap.
    eapply DSCut; first by eapply DAPInNil.
    d_forallp {t: CPLDeliver $ "n'" $ "m"}.
    eapply DSCut; first by eapply DSNotImpliesFalse with (Ac := {A:
                                                                   CPLDeliver $ "n'" $ "m" \in CNil}).

    d_swap; eapply DARewriteIffPL; first by d_head.
    rewrite_assertion_any; d_swap; d_clear.
      by d_ifp; first by d_head; d_false.

    by eapply DARewriteIffPL; first by apply DSMergeIf with
      (Ap1 := {A: self-event})
      (Ap2 := {A: on "n", (CPLDeliver $ "n'" $ "m" \in "Fois")})
      (Ac := {A: exists: "c":
        on "n", event [0]<- CSLDeliver $ "n'" $ ("c", "m")}).
  }

  (* By Lemma 96 on (1) and (2) *)
  d_have {A:
    on "n", event []<- CPLDeliver $ "n'" $ "m" <~
    exists: "c": on "n", event [0]<- CSLDeliver $ "n'" $ ("c", "m")
  }.
  {
    eapply DSCut;
    first by eapply DTL96_2 with (A1 := {A:
                                  on "n", event []<- CPLDeliver $ "n'" $ "m"})
                        (A2 := {A:
                                  (self-event /\ on "n", (CPLDeliver $ "n'" $ "m" \in "Fois"))})
                        (A3 := {A:
                                  exists: "c" : on "n", event [0]<- CSLDeliver $ "n'" $ (CPair $ "c" $ "m")}).
    d_ifp.
    d_splitc.
    d_swap.
    eapply DARewriteIfP. by apply DTL123 with (A := {A:
                                                       (self-event /\ on "n", (CPLDeliver $ "n'" $ "m" \in "Fois"))}).
    rewrite_assertion_pos.
    d_head. d_head. d_head.
  }

  (* By OR' *)
  d_have {A:
    forall: "c":
    on "n'", event [0]-> CSLSend $ "n" $ ("c", "m") =>>
    eventuallyp (self-event /\
      on "n'", ((0, CSLSend $ "n" $ ("c", "m")) \in "Fors"))
  }.
  {
    d_forallc "c".

    d_use DPOR'.
      d_forallp "n'"; d_forallp 0; d_forallp {t: CSLSend $ "n" $ (CPair $ "c" $ "m")}.
      (*
      d_have {A:
                 eventuallyp^ (self-event /\
                               "Fn" = "n'" /\ CPair $ 0 $ (CSLSend $ "n" $ (CPair $ "c" $ "m")) \in "Fors") =>>
                                                                                                             eventuallyp (self-event /\
                                                                                                                          "Fn" = "n'" /\ CPair $ 0 $ (CSLSend $ "n" $ (CPair $ "c" $ "m")) \in "Fors")}.
      {
        d_splitc.
        eapply DTL123.
       *)
    d_have {A: ("Fn" = "n'" /\ "Fd" = CCons $ 0 $ CNil /\ "Fo" = ORequest /\ "Fe" = CSLSend $ "n" $ (CPair $ "c" $ "m") =>>
                                                                                            eventuallyp (self-event /\ "Fn" = "n'" /\ CPair $ 0 $ (CSLSend $ "n" $ (CPair $ "c" $ "m")) \in "Fors"))}.
    {
      d_splitc.
      d_splitp; d_swap; d_clear.
      eapply DARewriteIfP with (Arp := {A: eventuallyp^ (self-event /\
                                                         "Fn" = "n'" /\ CPair $ 0 $ (CSLSend $ "n" $ (CPair $ "c" $ "m")) \in "Fors")})
                               (Arc := {A: eventuallyp (self-event /\
                                                        "Fn" = "n'" /\ CPair $ 0 $ (CSLSend $ "n" $ (CPair $ "c" $ "m")) \in "Fors")}).
      eapply DTL123.
      rewrite_assertion_pos.
      d_head.
      d_splitp; d_clear.
      eapply DARewriteIfP with (Arp := {A: eventuallyp^ (self-event /\
                                                         "Fn" = "n'" /\ CPair $ 0 $ (CSLSend $ "n" $ (CPair $ "c" $ "m")) \in "Fors")})
                               (Arc := {A: eventuallyp (self-event /\
                                                        "Fn" = "n'" /\ CPair $ 0 $ (CSLSend $ "n" $ (CPair $ "c" $ "m")) \in "Fors")}).
      eapply DTL123.
      rewrite_assertion_pos.
      d_head.
    }
    d_head.
  }

  (* By InvL *)
  d_have {A:
    forall: "c":
    self-event /\ on "n'", ((0, CSLSend $ "n" $ ("c", "m")) \in "Fors") =>>
    on "n'", event []-> CPLSend $ "n" $ ("m")
  }.
  {
    do 4 d_clear. (* Clean up the context *)

    (* Instantiate InvL *)
    eapply DSCut; first by apply DPInvL with
                      (A := {A:
                               on "n'", ((0, CSLSend $ "n" $ ("c", "m")) \in "Fors") ->
                                                                                     on "n'", event []-> CPLSend $ "n" $ ("m")
                      }); first by repeat constructor.

    (* Prove for requests *)
    d_ifp.
    d_forallc "e".
    d_ifc; d_splitp; d_swap. d_evalp.
    d_destructp (fun t => {A: ("Fs'" $ "Fn", "Fors", "Fois") = t}).
    d_forallp "r"; d_forallp "c".
    d_splitp; d_swap. d_substp. d_evalp.
    d_destructp (fun t => {A: ("Fs'" $ "Fn", "Fors", "Fois") = t}).
    d_forallp {t: ("m")}; d_forallp "n".
    d_splitp; d_swap.
    d_substp; d_evalp.
    d_destructtuplep
      {t: "Fs'" $ "Fn"} {t: "Fors"} {t: "Fois"}
      {t: (FSucc $ "c", "r")}
      {t: (CCons $ (CPair $ 0 $ (CSLSend $ "n" $ (CPair $ (FSucc $ "c") $ ("m")))) $ CNil)} {t: CNil}; do 2 d_splitp.
    d_ifc; d_splitp.
    d_splitc; first by d_head.
    d_rotate 7. do 2 (d_splitp; d_swap).
    d_splitc. do 2 d_rotate. d_head.
    d_splitc; d_swap; first by d_head.
    d_swap; d_substp; first by d_head.

    (* Prove for indications *)
    d_ifp.
    d_forallc "i"; d_forallc "e".
    d_ifc.
    d_splitp; d_swap; d_substp; d_evalp.
    d_destructp (fun t => {A: ("Fs'" $ "Fn", "Fors", "Fois") = t}).
    d_forallp "r"; d_forallp "c".
    d_splitp; d_swap. d_substp. d_evalp.
    d_destructp (fun t => {A: ("Fs'" $ "Fn", "Fors", "Fois") = t}).
    d_forallp "m". d_forallp "c'". d_forallp "n".
    d_splitp; d_swap.
    d_substp. d_evalp.
    d_destructp (fun t => {A: ("Fs'" $ "Fn", "Fors", "Fois") = t}).

    d_orp.
    (* true case *)
    d_splitp; d_swap.
    d_substp; d_evalp.
    d_destructtuplep
        {t: "Fs'" $ "Fn"} {t: "Fors"} {t: "Fois"}
        {t: ("c", "r")}
        {t:  CNil} {t: CNil}; do 2 d_splitp.
    d_ifc.
    d_subst.
    d_splitp; d_swap.
    eapply DSCut; first by eapply DAPInNil.
    d_forallp {t: CPair $ 0 $ (CSLSend $ "n" $ (CPair $ "c" $ "m"))}.
    eapply DSCut; first by eapply DSNotImpliesFalse with (Ac := {A:
                                                                   CPair $ 0 $ (CSLSend $ "n" $ (CPair $ "c" $ "m")) \in CNil}).
    d_swap; eapply DARewriteIffPL; first by d_head.
    rewrite_assertion_any; d_swap; d_clear.
      by d_ifp; first by d_head; d_false.

    (* false case *)
    d_splitp; d_swap.
    d_substp; d_evalp.
    d_destructtuplep
      {t: "Fs'" $ "Fn"} {t: "Fors"} {t: "Fois"}
      {t: (CPair $ "c" $ (FUnion $ "r" $ (CCons $ (CPair $ "n" $ "c'") $ CNil)))}
      {t:  CNil} {t: (CCons $ (CPLDeliver $ "n" $ "m") $ CNil)}; do 2 d_splitp.
    d_ifc; d_splitp; d_swap.
    d_substp.
    eapply DSCut; first by eapply DAPInNil.
    d_forallp {t: CPair $ 0 $ (CSLSend $ "n" $ (CPair $ "c" $ "m"))}.
    eapply DSCut; first by eapply DSNotImpliesFalse with (Ac := {A:
                                                                   CPair $ 0 $ (CSLSend $ "n" $ (CPair $ "c" $ "m")) \in CNil}).
    d_swap; eapply DARewriteIffPL; first by d_head.
    rewrite_assertion_any; d_swap; d_clear.
      by d_ifp; first by d_head; d_false.

    (* Prove for peridoics *)
    d_ifp.
    d_ifc. d_splitp. d_swap. d_evalp.
    d_destructtuplep
      {t: "Fs'" $ "Fn"} {t: "Fors"} {t: "Fois"}
      {t: "Fs" $ "Fn"}
      {t:  CNil} {t: CNil}; do 2 d_splitp.
    d_ifc; d_substp.
    d_splitp; d_swap.
    eapply DSCut; first by eapply DAPInNil.
    d_forallp {t: CPair $ 0 $ (CSLSend $ "n" $ (CPair $ "c" $ "m"))}.
    eapply DSCut; first by eapply DSNotImpliesFalse with (Ac := {A:
                                                                   CPair $ 0 $ (CSLSend $ "n" $ (CPair $ "c" $ "m")) \in CNil}).
    d_swap; eapply DARewriteIffPL; first by d_head.
    rewrite_assertion_any; d_swap; d_clear.
      by d_ifp; first by d_head; d_false.

    eapply DARewriteIffPL; first by apply DSMergeIf with
      (Ap1 := {A: self-event})
      (Ap2 := {A: on "n'", (CPair $ 0 $ (CSLSend $ "n" $ (CPair $ "c" $ "m")) \in "Fors")})
      (Ac := {A: on "n'", event []-> CPLSend $ "n" $ ("m")}).
    rewrite_assertion_any.
    d_forallc "c"; d_head.
  }

  (* By Lemma 96 on (4) and (5) *)
  d_have {A:
    forall: "c":
    on "n'", event [0]-> CSLSend $ "n" $ ("c", "m") <~
    on "n'", event []-> CPLSend $ "n" $ "m"
  }.
  {

    d_forallc "c".
    eapply DSCut;
      first by eapply DTL96_2 with
          (A1 := {A:
                    on "n'", event [0]-> CSLSend $ "n" $ ("c", "m")})
          (A2 := {A:
                    self-event /\ on "n'", (CPair $ 0 $ (CSLSend $ "n" $ (CPair $ "c" $ "m")) \in "Fors")})
          (A3 := {A:
                    on "n'", event []-> CPLSend $ "n" $ ("m")}).
    d_ifp.
    d_splitc.
    d_swap.
    d_forallp "c". d_head.
    d_forallp "c". d_head.
    d_head.
  }

  (* By PL_SL_2 *)
  d_have {A:
    exists: "c":
    on "n", event [0]<- CSLDeliver $ "n'" $ ("c", "m") <~
    on "n'", event [0]-> CSLSend $ "n" $ ("c", "m")
  }.
  {
    do 6 d_clear. (* Clean up the context *)
    d_have (derives_assertion PL_SL_2); first by
      d_clearv "n"; d_clearv "n'"; d_clearv "m";
      apply PL_SL_2.
    by d_existsc "c";
      d_forallp "n"; d_forallp "n'"; d_forallp {t: ("c", "m")}.
  }

  (* From Lemma 85 on (3), PL_SL_2, and (6) *)
  d_have {A:
            exists: "c": on "n", event []<- CPLDeliver $ "n'" $ "m" <~
                          on "n'", event [0]-> CSLSend $ "n" $ (CPair $ "c" $ "m")
         }.
  d_existsc "c".
  eapply DTL85 with
             (A1 := {A: on "n", event []<- CPLDeliver $ "n'" $ "m"})
             (A2 := {A: on "n", event [0]<- CSLDeliver $ "n'" $ ("c", "m")})
             (A3 := {A: on "n'", event [0]-> CSLSend $ "n" $ ("c", "m")}).
  - d_rotate 4.
    d_have {A:
              (exists: "c" : on "n", event [0]<- CSLDeliver $ "n'" $ (CPair $ "c" $ "m")) =>>
                                           on "n", event [0]<- CSLDeliver $ "n'" $ (CPair $ "c" $ "m")}.
    eapply DTGeneralization; first by repeat constructor.
    d_ifc. d_existsp "c". d_head.
    d_swap.
    eapply DARewriteEntailsP with (Arp := {A: exists: "c" : on "n", event [0]<- CSLDeliver $ "n'" $ (CPair $ "c" $ "m")})
                                  (Arc := {A: on "n", event [0]<- CSLDeliver $ "n'" $ (CPair $ "c" $ "m")}).
    d_head.
    rewrite_assertion_pos.
    d_head.
  -
    d_existsp "c".
    d_head.

  d_have {A:
            on "n", event []<- CPLDeliver $ "n'" $ "m" <~
                          on "n'", event []-> CPLSend $ "n" $ "m"}.
  d_existsp "c".
  eapply DTL85.
  - by [].
  - d_rotate 2.
    d_forallp "c".
    d_head.
  d_head.
Qed.
