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
    match: #(1, 0) with:
    {{ (slc, CPLDeliver $ # $ (#, #)) (* n, c', m *) ->
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
      if: (n, c') \in r
      then:
        (s, [], [])
      else:
        let: # := r \union [(n, c')] in: (* r' *)
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
        let: # := CPLDeliver $ n $ m in: (* oi *)
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
        ((c, r'), [], [oi])
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
    forall: "n", "n'", "m":
    correct "n" /\ correct "n'" ->
    on "n", event [0]-> CSLSend $ "n'" $ "m" =>>
    always eventually on "n'", event [0]<- CSLDeliver $ "n" $ "m"
  }.
Proof.
  d_forallc "n"; d_forallc "n'"; d_forallc "m".

  (* Use the lowering specification on SL_1 *)
  eapply DSCut; first by apply: DPLower SL_1 perfect_link 0 SL_1_TA.
  rewrite /lower_assertion /=.

  eapply DARewriteEntailsP; first by apply DTL124 with
    (Ap := {A: "Fd" <<< [0]})
    (Ac := {A: eventually on "n'", event [0]<- CSLDeliver $ "n" $ "m"}).
  eapply DARewriteEntailsP; first by apply DTL124 with
    (Ap := {A: "Fd" <<< [0]})
    (Ac := {A:
      on "n", event [0]-> CSLSend $ "n'" $ "m" ->
      "Fd" <<< [0] ~>
      on "n'", event [0]<- CSLDeliver $ "n" $ "m"}).
  eapply DARewriteIffPL; first by apply DSMergeIf with
    (Ap1 := {A: "Fd" <<< [0]})
    (Ap2 := {A: on "n", event [0]-> CSLSend $ "n'" $ "m"})
    (Ac := {A:
      "Fd" <<< [0] ~>
      on "n'", event [0]<- CSLDeliver $ "n" $ "m"
    }).
  eapply DARewriteIfP; first by apply DT1 with
    (A := {A:
      "Fd" <<< [0] ->
      eventually on "n'", event [0]<- CSLDeliver $ "n" $ "m"}).

  d_have {A:
    "Fd" <<< [0] /\ on "n", event [0]-> CSLSend $ "n'" $ "m" <->
    on "n", event [0]-> CSLSend $ "n'" $ "m"
  }.
  {
    d_splitc; d_ifc.
    - by d_splitp; d_swap; d_head.
    - d_splitc.
      + by d_splitp; d_swap; d_splitp; d_substc; eapply DAPExtension.
      + by d_head.
  }

  d_swap; eapply DARewriteIffPL; first by (d_head); d_swap.

  eapply DARewriteIffPL; first by apply DSMergeIf with
    (Ap1 := {A: on "n", event [0]-> CSLSend $ "n'" $ "m"})
    (Ap2 := {A: "Fd" <<< [0]})
    (Ac := {A:
      eventually on "n'", event [0]<- CSLDeliver $ "n" $ "m"
    }).
  eapply DARewriteIffPL; first by apply DSAndCommutative with
    (Acl := {A: on "n", event [0]-> CSLSend $ "n'" $ "m"})
    (Acr := {A: "Fd" <<< CCons $ 0 $ CNil}).
  eapply DARewriteIffPL; first by d_head.
  rewrite_assertion_any.

  by eapply DARewriteEntailsC; first by apply DTL80 with
    (A := {A: eventually on "n'", event [0]<- CSLDeliver $ "n" $ "m"}).
Qed.

Definition PL_SL_2 :
  Context [::] [::] |- perfect_link, {A:
    forall: "n", "n'", "m":
    on "n", event [0]<- CSLDeliver $ "n'" $ "m" <~
    on "n'", event [0]-> CSLSend $ "n" $ "m"
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
    [:: V "m'"; V "c"; V "m"; V "n'"; V "n"]
    [:: {A: correct "n"}; {A: correct "n'"}] |- perfect_link, {A:
    self-event /\ on "n", ((0, CSLSend $ "n'" $ ("c", "m")) \in "Fors") =>>
    always^ ~(self-event /\
      on "n", ((0, CSLSend $ "n'" $ ("c", "m'")) \in "Fors"))
  }.
Proof.
Admitted. (* TODO *)

Lemma L37_2 :
  Context
    [:: V "m'"; V "c"; V "m"; V "n'"; V "n"]
    [:: {A: correct "n"}; {A: correct "n'"}] |- perfect_link, {A:
    self-event /\ on "n", ((0, CSLSend $ "n'" $ ("c", "m")) \in "Fors") =>>
    alwaysp^ ~(self-event /\
      on "n", ((0, CSLSend $ "n'" $ ("c", "m'")) \in "Fors"))
  }.
Proof.
Admitted. (* TODO *)

Lemma L38 :
  Context
    [:: V "c"; V "m"; V "n'"; V "n"]
    [:: {A: correct "n"}; {A: correct "n'"}] |- perfect_link, {A:
    on "n'", event [0]<- CSLDeliver $ "n" $ ("c", "m") =>>
    eventually on "n'", event []<- CPLDeliver $ "n" $ "m" \/
    exists: "m": eventuallyp (
      on "n", event []-> CPLSend $ "n" $ "m" /\
      eventually on "n'", event []<- CPLDeliver $ "n" $ "m"
    )
  }.
Proof.
Admitted. (* TODO *)

Lemma L39 :
  Context
    [:: V "c"; V "m"; V "n'"; V "n"]
    [:: {A: correct "n"}; {A: correct "n'"}] |- perfect_link, {A:
    on "n'", event [0]<- CSLDeliver $ "n" $ ("c", "m") /\
    ("n", "c") \notin (FRight $ ("Fs" $ "n'")) =>>
    eventually on "n'", event []<- CPLDeliver $ "n" $ "m"
  }.
Proof.
Admitted. (* TODO *)

Lemma L40 :
  Context
    [:: V "c"; V "m"; V "n'"; V "n"]
    [:: {A: correct "n"}; {A: correct "n'"}] |- perfect_link, {A:
    self-event /\ "Fn" = "n'" /\ ("n", "c") \in (FRight $ ("Fs" $ "n'")) =>>
    exists: "m": eventuallyp (
      on "n", ((0, CSLSend $ "n'" $ ("c", "m")) \in "Fors") /\
      self-event /\
      eventually on "n'", event []<- CPLDeliver $ "n" $ "m"
    )
  }.
Proof.
Admitted. (* TODO *)

Lemma L41 :
  Context
    [:: V "c"; V "m"; V "n'"; V "n"]
    [:: {A: correct "n"}; {A: correct "n'"}] |- perfect_link, {A:
    self-event /\ ("n", "c") \in (FRight $ ("Fs" $ "n'")) =>>
    exists: "m": eventuallyp (
      on "n'", event [0]<- CSLDeliver $ "n" $ ("c", "m") /\
      (CPLDeliver $ "n" $ "m") \in "Fois"
    )
  }.
Proof.
Admitted. (* TODO *)

(* Reliable delivery
 * If a correct node n sends a message m to a correct node n', then n' will
 * eventually deliver m.
 *)
Theorem PL_1 : Context [:: V "m"; V "n'"; V "n"] [::] |- perfect_link, {A:
  correct "n" /\ correct "n'" ->
  on "n", event []-> CPLSend $ "n'" $ "m" ~>
  on "n'", event []<- CPLDeliver $ "n" $ "m"
}.
Proof.
  (* Introduce context *)
  set C := perfect_link.
  d_ifc; d_splitp.
Admitted. (* TODO *)

(* Lemmas used in proving PL_2 *)

Lemma L42 :
  Context
    [:: V "m"; V "n'"; V "n"]
    [:: {A: correct "n"}; {A: correct "n'"}] |- perfect_link, {A:
    self (
      "Fn" = "n" /\ (CPLDeliver $ "n'" $ "m") \in "Fois" =>>
      always^ ("Fn" = "n" -> (CPLDeliver $ "n'" $ "m") \notin "Fois") /\
      alwaysp^ ("Fn" = "n" -> (CPLDeliver $ "n'" $ "m") \notin "Fois")
    )
  }.
Proof.
Admitted. (* TODO *)

Lemma L43 :
  Context
    [:: V "c"; V "m"; V "n'"; V "n"]
    [:: {A: correct "n"}; {A: correct "n'"}] |- perfect_link, {A:
    self (
      ("n'", "c") \in (FRight $ ("Fs" $ "n")) /\
      eventuallyp on "n", event [0]<- CSLDeliver $ "n'" $ ("c", "m") =>>
      "Fn" = "n" -> (CPLDeliver $ "n'" $ "m") \notin "Fois"
    )
  }.
Proof.
Admitted. (* TODO *)

Lemma L44 :
  Context
    [:: V "c'"; V "c"; V "m"; V "n'"; V "n"]
    [:: {A: correct "n"}; {A: correct "n'"}] |- perfect_link, {A:
    self (
      on "n", event [0]<- CSLDeliver $ "n'" $ ("c", "m") /\
      eventuallyp on "n", event [0]<- CSLDeliver $ "n'" $ ("c'", "m") =>>
      "c" = "c'"
    )
  }.
Proof.
Admitted. (* TODO *)

(* No-duplication
 * If a message is sent at most once, it will be delivered at most once.
 *)
Theorem PL_2 : Context [:: V "m"; V "n'"; V "n"] [::] |- perfect_link, {A:
  (on "n'", event []-> CPLSend $ "n" $ "m" =>>
    alwaysp^ ~on "n'", event []-> CPLSend $ "n" $ "m") ->
  (on "n", event []<- CPLDeliver $ "n'" $ "m" =>>
    alwaysp^ ~on "n", event []<- CPLDeliver $ "n'" $ "m")
}.
Proof.
Admitted. (* TODO *)

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
      admit.

    (* Prove for indications *)
    d_ifp.
      admit.

    (* Prove for periodics *)
    d_ifp.
      admit.

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
    admit.
  }

  (* By OR' *)
  d_have {A:
    forall: "c":
    on "n'", event [0]-> CSLSend $ "n" $ ("c", "m") =>>
    eventuallyp (self-event /\
      on "n'", ((0, CSLSend $ "n" $ ("c", "m")) \in "Fors"))
  }.
  {
    do 3 d_clear. (* Clean up the context *)

    admit.
  }

  (* By InvL *)
  d_have {A:
    forall: "c":
    self-event /\ on "n'", ((0, CSLSend $ "n" $ ("c", "m")) \in "Fors") =>>
    on "n'", event []-> CPLSend $ "n" $ ("c", "m")
  }.
  {
    do 4 d_clear. (* Clean up the context *)

    admit.
  }

  (* By Lemma 96 on (4) and (5) *)
  d_have {A:
    forall: "c":
    on "n'", event [0]-> CSLSend $ "n" $ ("c", "m") <~
    on "n'", event []-> CPLSend $ "n" $ "m"
  }.
  {
    admit.
  }

  (* By PL_SL_2 *)
  d_have {A:
    forall: "c":
    on "n", event [0]<- CSLDeliver $ "n'" $ ("c", "m") <~
    on "n'", event [0]-> CSLSend $ "n" $ ("c", "m")
  }.
  {
    do 6 d_clear. (* Clean up the context *)
    d_have (derives_assertion PL_SL_2); first by
      d_clearv "n"; d_clearv "n'"; d_clearv "m";
      apply PL_SL_2.
    by d_forallc "c";
      d_forallp "n"; d_forallp "n'"; d_forallp {t: ("c", "m")}.
  }

  (* From Lemma 85 on (3), PL_SL_2, and (6) *)
Admitted. (* TODO *)
