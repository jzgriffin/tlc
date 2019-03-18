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
Definition PL_SL_1 := DPLower SL_1 perfect_link 0 SL_1_TI.
Definition PL_SL_2 := DPLower SL_2 perfect_link 0 SL_2_TI.

(* Lemmas used in proving PL_1 *)

Lemma L37_1 :
  Context
    [:: V "m'"; V "c"; V "n"; V "n'"; V "m"]
    [:: {A: correct "n"}; {A: correct "n'"}] |- perfect_link, {A:
    when-self /\ when-on["n"] ((0, CSLSend $ "n'" $ ("c", "m")) \in "Fors") =>>
    always^ ~(when-self /\
      when-on["n"] ((0, CSLSend $ "n'" $ ("c", "m'")) \in "Fors"))
  }.
Proof.
Admitted. (* TODO *)

Lemma L37_2 :
  Context
    [:: V "m'"; V "c"; V "n"; V "n'"; V "m"]
    [:: {A: correct "n"}; {A: correct "n'"}] |- perfect_link, {A:
    when-self /\ when-on["n"] ((0, CSLSend $ "n'" $ ("c", "m")) \in "Fors") =>>
    alwaysp^ ~(when-self /\
      when-on["n"] ((0, CSLSend $ "n'" $ ("c", "m'")) \in "Fors"))
  }.
Proof.
Admitted. (* TODO *)

Lemma L38 :
  Context
    [:: V "c"; V "n"; V "n'"; V "m"]
    [:: {A: correct "n"}; {A: correct "n'"}] |- perfect_link, {A:
    when-on["n'"] when[0]<- CSLDeliver $ "n" $ ("c", "m") =>>
    eventually when-on["n'"] when[]<- CPLDeliver $ "n" $ "m" \/
    exists: "m": eventuallyp (
      when-on["n"] when[]-> CPLSend $ "n" $ "m" /\
      eventually when-on["n'"] when[]<- CPLDeliver $ "n" $ "m"
    )
  }.
Proof.
Admitted. (* TODO *)

Lemma L39 :
  Context
    [:: V "c"; V "n"; V "n'"; V "m"]
    [:: {A: correct "n"}; {A: correct "n'"}] |- perfect_link, {A:
    when-on["n'"] when[0]<- CSLDeliver $ "n" $ ("c", "m") /\
    ("n", "c") \notin (FRight $ ("Fs" $ "n'")) =>>
    eventually when-on["n'"] when[]<- CPLDeliver $ "n" $ "m"
  }.
Proof.
Admitted. (* TODO *)

Lemma L40 :
  Context
    [:: V "c"; V "n"; V "n'"; V "m"]
    [:: {A: correct "n"}; {A: correct "n'"}] |- perfect_link, {A:
    when-self /\ "Fn" = "n'" /\ ("n", "c") \in (FRight $ ("Fs" $ "n'")) =>>
    exists: "m": eventuallyp (
      when-on["n"] ((0, CSLSend $ "n'" $ ("c", "m")) \in "Fors") /\
      when-self /\
      eventually when-on["n'"] when[]<- CPLDeliver $ "n" $ "m"
    )
  }.
Proof.
Admitted. (* TODO *)

Lemma L41 :
  Context
    [:: V "c"; V "n"; V "n'"; V "m"]
    [:: {A: correct "n"}; {A: correct "n'"}] |- perfect_link, {A:
    when-self /\ ("n", "c") \in (FRight $ ("Fs" $ "n'")) =>>
    exists: "m": eventuallyp (
      when-on["n'"] when[0]<- CSLDeliver $ "n" $ ("c", "m") /\
      (CPLDeliver $ "n" $ "m") \in "Fois"
    )
  }.
Proof.
Admitted. (* TODO *)

(* Reliable delivery
 * If a correct node n sends a message m to a correct node n', then n' will
 * eventually deliver m.
 *)
Theorem PL_1 : Context [:: V "n"; V "n'"; V "m"] [::] |- perfect_link, {A:
  correct "n" /\ correct "n'" ->
  when-on["n"] when[]-> CPLSend $ "n'" $ "m" ~>
  when-on["n'"] when[]<- CPLDeliver $ "n" $ "m"
}.
Proof.
  (* Introduce context *)
  set C := perfect_link.
  d_ifc; d_splitp.
Admitted. (* TODO *)

(* Lemmas used in proving PL_2 *)

Lemma L42 :
  Context
    [:: V "n"; V "n'"; V "m"]
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
    [:: V "c"; V "n"; V "n'"; V "m"]
    [:: {A: correct "n"}; {A: correct "n'"}] |- perfect_link, {A:
    self (
      ("n'", "c") \in (FRight $ ("Fs" $ "n")) /\
      eventuallyp when-on["n"] when[0]<- CSLDeliver $ "n'" $ ("c", "m") =>>
      "Fn" = "n" -> (CPLDeliver $ "n'" $ "m") \notin "Fois"
    )
  }.
Proof.
Admitted. (* TODO *)

Lemma L44 :
  Context
    [:: V "c'"; V "c"; V "n"; V "n'"; V "m"]
    [:: {A: correct "n"}; {A: correct "n'"}] |- perfect_link, {A:
    self (
      when-on["n"] when[0]<- CSLDeliver $ "n'" $ ("c", "m") /\
      eventuallyp when-on["n"] when[0]<- CSLDeliver $ "n'" $ ("c'", "m") =>>
      "c" = "c'"
    )
  }.
Proof.
Admitted. (* TODO *)

(* No-duplication
 * If a message is sent at most once, it will be delivered at most once.
 *)
Theorem PL_2 : Context [:: V "n"; V "n'"; V "m"] [::] |- perfect_link, {A:
  (when-on["n'"] when[]-> CPLSend $ "n" $ "m" =>>
    alwaysp^ ~when-on["n'"] when[]-> CPLSend $ "n" $ "m") ->
  (when-on["n"] when[]<- CPLDeliver $ "n'" $ "m" =>>
    alwaysp^ ~when-on["n"] when[]<- CPLDeliver $ "n'" $ "m")
}.
Proof.
Admitted. (* TODO *)

(* No-forge
 * If a node n delivers a message m with sender n', then m was previously sent
 * to n by node n'.
 *)
Theorem PL_3 : Context [:: V "n"; V "n'"; V "m"] [::] |- perfect_link, {A:
  when-on["n"] when[]<- CPLDeliver $ "n'" $ "m" <~
  when-on["n'"] when[]-> CPLSend $ "n" $ "m"
}.
Proof.
  (* By OI' *)
  d_have {A:
    when-on["n"] when[]<- CPLDeliver $ "n'" $ "m" =>>
    eventuallyp^ (when-on["n"]
      ((CPLDeliver $ "n'" $ "m") \in "Fois") /\ when-self)
  }.
  {
    (* Instantiate OI' *)
    eapply DSCut; first by apply DPOI'.
    by d_forallp "n"; d_forallp {t: CPLDeliver $ "n'" $ "m"}; d_head.
  }

  (* By InvL *)
  d_have {A:
    when-on["n"] (CPLDeliver $ "n'" $ "m" \in "Fois") /\ when-self =>>
    exists: "c": when-on["n"] when[0]<- CSLDeliver $ "n'" $ ("c", "m")
  }.
  {
    d_clear. (* Clean up the context *)

    (* Instantiate InvL *)
    eapply DSCut; first by apply DPInvL with (A := {A:
        when-on["n"] (CPLDeliver $ "n'" $ "m" \in "Fois") ->
        exists: "c": when-on["n"] when[0]<- CSLDeliver $ "n'" $ ("c", "m")
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

    eapply DARewriteIffPL; first by apply DSMergeIf with
      (Ap1 := {A: when-self})
      (Ap2 := {A: when-on["n"] (CPLDeliver $ "n'" $ "m" \in "Fois")})
      (Ac := {A: exists: "c":
        when-on["n"] when[0]<- CSLDeliver $ "n'" $ ("c", "m")}).
    by eapply DARewriteIffPL; first by apply DSAndCommutative with
      (Acl := {A: when-self})
      (Acr := {A: when-on["n"] (CPLDeliver $ "n'" $ "m" \in "Fois")}).
  }

  (* By Lemma 96 on (1) and (2) *)
  d_have {A:
    when-on["n"] when[]<- CPLDeliver $ "n'" $ "m" <~
    exists: "c": when-on["n"] when[0]<- CSLDeliver $ "n'" $ ("c", "m")
  }.
  {
    admit.
  }

  (* By OR' *)
  d_have {A:
    forall: "c":
    when-on["n'"] when[0]-> CSLSend $ "n" $ ("c", "m") =>>
    eventuallyp (
      when-on["n'"] ((0, CSLSend $ "n" $ ("c", "m")) \in "Fors") /\
      when-self
    )
  }.
  {
    do 3 d_clear. (* Clean up the context *)

    admit.
  }

  (* By InvL *)
  d_have {A:
    forall: "c":
    when-on["n'"] ((0, CSLSend $ "n" $ ("c", "m")) \in "Fors") /\ when-self =>>
    when-on["n'"] when[]-> CPLSend $ "n" $ ("c", "m")
  }.
  {
    do 4 d_clear. (* Clean up the context *)

    admit.
  }

  (* By Lemma 96 on (4) and (5) *)
  d_have {A:
    forall: "c":
    when-on["n'"] when[0]-> CSLSend $ "n" $ ("c", "m") <~
    when-on["n'"] when[]-> CPLSend $ "n" $ "m"
  }.
  {
    admit.
  }

  (* From Lemma 85 on (3), PL_SL_2, and (6) *)
Admitted. (* TODO *)
