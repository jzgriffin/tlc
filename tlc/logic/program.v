(* TLC in Coq
 *
 * Module: tlc.logic.program
 * Purpose: Contains derived rules and lemmas regarding the program logic.
 *)

Require Import mathcomp.ssreflect.seq.
Require Import mathcomp.ssreflect.ssreflect.
Require Import tlc.component.component.
Require Import tlc.logic.context.
Require Import tlc.logic.derives.
Require Import tlc.logic.sequent.
Require Import tlc.operation.periodic_event.
Require Import tlc.semantics.all_semantics.
Require Import tlc.syntax.all_syntax.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* These rules and lemmas are taken directly from the appendix *)

Lemma DPIROI C ctx (S : term -> assertion) :
  ctx |- C, {A:
    forall: "n", "e", "e'":
    (
      forall: "s":
      S "s" /\
      "e'" \in let: (%, %, #) := request C $ "n" $ "s" $ "e" in: #(0, 0)
    ) ->
    (
      on "n", event []-> "e" /\ S {t: "Fs" $ "n"} =>>
      eventually on "n", event []<- "e'"
    )
  }.
Proof.
Admitted. (* TODO *)

Lemma DPIIOI C ctx (S : term -> assertion) :
  ctx |- C, {A:
    forall: "n", "i", "e", "e'":
    (
      forall: "s":
      S "s" /\
      "e'" \in let: (%, %, #) := indication C $ "n" $ "s" $ ("i", "e") in: #(0, 0)
    ) ->
    (
      on "n", event ["i"]<- "e" /\ S {t: "Fs" $ "n"} =>>
      eventually^ on "n", event []<- "e'"
    )
  }.
Proof.
Admitted. (* TODO *)

Lemma DPInvL C ctx A :
  non_temporal_assertion A ->
  ctx |- C, {A:
    (
      forall: "e":
      event []-> "e" /\
      ("Fs'" $ "Fn", "Fors", "Fois") =
        request C $ "Fn" $ ("Fs" $ "Fn") $ "e" ->
      A
    ) ->
    (
      forall: "i", "e":
      event ["i"]<- "e" /\
      ("Fs'" $ "Fn", "Fors", "Fois") =
        indication C $ "Fn" $ ("Fs" $ "Fn") $ ("i", "e") ->
      A
    ) ->
    (
      event []~> PE /\
      ("Fs'" $ "Fn", "Fors", "Fois") =
        periodic C $ "Fn" $ ("Fs" $ "Fn") ->
      A
    ) ->
    (
      self-event =>> A
    )
  }.
Proof.
Admitted. (* TODO *)

Lemma DPInvLSE C ctx A :
  non_temporal_assertion A ->
  ctx |- C, {A:
    (
      forall: "e":
      event []-> "e" /\
      ("Fs'" $ "Fn", "Fors", "Fois") =
        request C $ "Fn" $ ("Fs" $ "Fn") $ "e" ->
      A
    ) ->
    (
      forall: "i", "e":
      event ["i"]<- "e" /\
      ("Fs'" $ "Fn", "Fors", "Fois") =
        indication C $ "Fn" $ ("Fs" $ "Fn") $ ("i", "e") ->
      A
    ) ->
    (
      event []~> PE /\
      ("Fs'" $ "Fn", "Fors", "Fois") =
        periodic C $ "Fn" $ ("Fs" $ "Fn") ->
      A
    ) ->
    (
      self (always A)
    )
  }.
Proof.
Admitted. (* TODO *)

Lemma DPInvS C ctx (S : term -> assertion) :
  ctx |- C, {A:
    forall: "n":
    (
      forall: "s", "e":
      S "s" ->
      S {t: let: (#, %, %) := request C $ "n" $ "s" $ "e" in: #(0, 0)}
    ) ->
    (
      forall: "s", "i", "e":
      S "s" ->
      S {t: let: (#, %, %) := indication C $ "n" $ "s" $ ("i", "e") in: #(0, 0)}
    ) ->
    (
      forall: "s":
      S "s" ->
      S {t: let: (#, %, %) := periodic C $ "n" $ "s" in: #(0, 0)}
    ) ->
    (
      self-event /\ S {t: "Fs" $ "n"} =>>
                      self-event =>> S {t: "Fs" $ "n"}
    )
  }.
Proof.
Admitted. (* TODO *)

Lemma DPInvSSe C ctx (S : term -> assertion) :
  ctx |- C, {A:
    forall: "n":
    (
      forall: "s", "e":
      S "s" ->
      S {t: let: (#, %, %) := request C $ "n" $ "s" $ "e" in: #(0, 0)}
    ) ->
    (
      forall: "s", "i", "e":
      S "s" ->
      S {t: let: (#, %, %) := indication C $ "n" $ "s" $ ("i", "e") in: #(0, 0)}
    ) ->
    (
      forall: "s":
      S "s" ->
      S {t: let: (#, %, %) := periodic C $ "n" $ "s" in: #(0, 0)}
    ) ->
    (
      self ((S {t: "Fs" $ "n"}) =>> always (S {t: "Fs" $ "n"}))
    )
  }.
Proof.
Admitted. (* TODO *)

Lemma DPInvS'' C ctx (S : term -> assertion) :
  ctx |- C, {A:
    forall: "n":
    (
      forall: "s", "e":
      S "s" ->
      S {t: let: (#, %, %) := request C $ "n" $ "s" $ "e" in: #(0, 0)}
    ) ->
    (
      forall: "s", "i", "e":
      S "s" ->
      S {t: let: (#, %, %) := indication C $ "n" $ "s" $ ("i", "e") in: #(0, 0)}
    ) ->
    (
      forall: "s":
      S "s" ->
      S {t: let: (#, %, %) := periodic C $ "n" $ "s" in: #(0, 0)}
    ) ->
    (
      self-event /\ S {t: "Fs'" $ "n"} =>>
      always^ (self-event -> S {t: "Fs" $ "n"})
    )
  }.
Proof.
Admitted. (* TODO *)

Lemma DPInvSA C ctx (S : term -> assertion) A :
  non_temporal_assertion A ->
  ctx |- C, {A:
    forall: "?n":
    ~(S {t: initialize C $ "?n"}) ->
    (
      forall: "?e":
      on "?n", event []-> "?e" /\
      ~(S {t: "Fs" $ "?n"}) /\
      S {t: let: (#, %, %) :=
        request C $ "?n" $ ("Fs" $ "?n") $ "?e" in: #(0, 0)} ->
      A
    ) ->
    (
      forall: "?i", "?e":
      on "?n", event ["?i"]<-"?e" /\
      (("Fs'" $ "Fn", "Fors", "Fois") =
        indication C $ "Fn" $ ("Fs" $ "Fn") $ ("?i", "?e")) /\
      ~(S {t: "Fs" $ "?n"}) /\
      S {t: let: (#, %, %) :=
        indication C $ "?n" $ ("Fs" $ "?n") $ ("?i", "?e") in: #(0, 0)} ->
      A
    ) ->
    (
      on "?n", event []~> PE /\
      (("Fs'" $ "Fn", "Fors", "Fois") = periodic C $ "Fn" $ ("Fs" $ "Fn")) /\
      ~(S {t: "Fs" $ "?n"}) /\
      S {t: "Fs'" $ "Fn"} ->
      A
    ) ->
    (
      (self-event /\ S {t: "Fs" $ "?n"}) =>> eventuallyp^ on "?n", A
    )
  }.
Proof.
Admitted. (* TODO *)

Lemma DPAPerSA C ctx (S : term -> assertion) A :
  non_temporal_assertion A ->
  ctx |- C, {A:
    forall: "n":
    (
      "Fn" = "n" /\
      self-event /\
      S {t: "Fs" $ "n"} /\
      ("Fs'" $ "n", "Fors", "Fois") = periodic C $ "n" $ ("Fs" $ "n") ->
      A
    ) ->
    (
      correct "n" ->
      (self-event -> S {t: "Fs" $ "n"}) =>>
      always eventually A
    )
  }.
Proof.
Admitted. (* TODO *)

(* These rules are specific to this implementation *)

Lemma DPLower :
  forall C' Delta A,
  Context Delta [::] |- C', A ->
  forall C i (TA : top_assertion A),
  Context Delta [::] |- C, lower_assertion i TA.
Proof.
Admitted. (* TODO *)

Lemma DPTopRequestSelf C ctx :
  ctx |- C, {A:
    forall: "e":
    event []-> "e" =>> self-event
  }.
Proof.
Admitted. (* TODO *)

Lemma DPTopRequestSelfEliminate C ctx :
  ctx |- C, {A:
    forall: "e":
    event []-> "e" /\ self-event <-> event []-> "e"
  }.
Proof.
  case: ctx => Delta Gamma.
  d_forallc "e"; d_splitc; d_ifc.
  - by d_splitp; d_head.
  - d_splitc; first by d_head.
  - d_splitp; d_swap; d_splitp; d_right; d_left; d_splitc.
    + by d_clear; d_clear; d_head.
    + by d_head.
Qed.

Lemma DPSecondIndicationSelf C ctx :
  ctx |- C, {A: forall: "e": event [0]<- "e" =>> self-event}.
Proof.
Admitted. (* TODO *)

Lemma DPSecondIndicationSelfEliminate C ctx :
  ctx |- C, {A:
    forall: "e":
    event [0]<- "e" /\ self-event <-> event [0]<- "e"
  }.
Proof.
Admitted. (* TODO *)

Lemma DPASA C ctx (S : term -> assertion) A A':
  non_temporal_assertion A ->
  ctx |- C, {A:
    forall: "n":
    (self-event /\ A =>> S {t: "Fs'" $ "n"}) ->
    (self-event /\ S {t: "Fs" $ "n"} =>> (self-event =>> A')) ->
    (self-event /\ A =>> always^ (self-event -> A'))
  }.
Proof.
Admitted. (* TODO *)

Lemma DPASASe C ctx (S : term -> assertion) A A':
  ctx |- C, {A:
    forall: "n":
    self (A =>> S {t: "Fs'" $ "n"}) ->
    self (S {t: "Fs" $ "n"} =>> (always A')) ->
    self (A =>> always^ (A'))
  }.
Proof.
Admitted. (* TODO *)

Lemma DPInvSe C ctx (S : term -> assertion) A :
  ctx |- C, {A:
    (
      self (forall: "e": event []-> "e" =>> A)
    ) ->
    (
      self (forall: "i", "e": event ["i"]<- "e" =>> A)
    ) ->
    (
      self (event []~> PE =>> A)
    ) ->
    (
      self (always (A))
    )
  }.
Proof.
Admitted. (* TODO *)
