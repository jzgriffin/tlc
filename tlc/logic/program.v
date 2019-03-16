(* TLC in Coq
 *
 * Module: tlc.logic.program
 * Purpose: Contains derived rules and lemmas regarding the program logic.
 *)

Require Import mathcomp.ssreflect.ssreflect.
Require Import tlc.component.component.
Require Import tlc.logic.derives.
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
      "e'" \in let: (%, %, #) := request C $ "n" $ "s" $ "e" in: #0
    ) ->
    (
      when-on["n"] when[]-> "e" /\ S {t: "Fs" $ "n"} =>>
      eventually when-on["n"] when[]<- "e'"
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
      "e'" \in let: (%, %, #) := indication C $ "n" $ "s" $ ("i", "e") in: #0
    ) ->
    (
      when-on["n"] when["i"]<- "e" /\ S {t: "Fs" $ "n"} =>>
      eventually^ when-on["n"] when[]<- "e'"
    )
  }.
Proof.
Admitted. (* TODO *)

Lemma DPInvL C ctx A :
  non_temporal_assertion A ->
  ctx |- C, {A:
    (
      forall: "e":
      when[]-> "e" /\
      ("Fs'" $ "Fn", "Fors", "Fois") =
        request C $ "Fn" $ ("Fs" $ "Fn") $ "e" ->
      A
    ) ->
    (
      forall: "i", "e":
      when["i"]<- "e" /\
      ("Fs'" $ "Fn", "Fors", "Fois") =
        indication C $ "Fn" $ ("Fs" $ "Fn") $ ("i", "e") ->
      A
    ) ->
    (
      when[]~> PE /\
      ("Fs'" $ "Fn", "Fors", "Fois") =
        periodic C $ "Fn" $ ("Fs" $ "Fn") ->
      A
    ) ->
    (
      when-self =>> A
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
      S {t: let: (#, %, %) := request C $ "n" $ "s" $ "e" in: #0}
    ) ->
    (
      forall: "s", "i", "e":
      S "s" ->
      S {t: let: (#, %, %) := indication C $ "n" $ "s" $ ("i", "e") in: #0}
    ) ->
    (
      forall: "s":
      S "s" ->
      S {t: let: (#, %, %) := periodic C $ "n" $ "s" in: #0}
    ) ->
    (
      when-self /\ S {t: "Fs'" $ "n"} =>>
      always^ (when-self -> S {t: "Fs" $ "n"})
    )
  }.
Proof.
Admitted. (* TODO *)

Lemma DPInvSA C ctx (S : term -> assertion) A :
  non_temporal_assertion A ->
  ctx |- C, {A:
    forall: "n":
    ~(S {t: initialize C $ "n"}) ->
    (
      forall: "e":
      when-on["n"] when[]-> "e" /\
      ~(S {t: "Fs" $ "n"}) /\
      S {t: let: (#, %, %) := request C $ "n" $ ("Fs" $ "n") $ "e" in: #0} ->
      A
    ) ->
    (
      forall: "i", "e":
      when-on["n"] when["i"]<-"e" /\
      ~(S {t: "Fs" $ "n"}) /\
      S {t: let: (#, %, %) :=
        indication C $ "n" $ ("Fs" $ "n") $ ("i", "e") in: #0} ->
      A
    ) ->
    (
      when-on["n"] when[]~> PE /\
      ~(S {t: "Fs" $ "n"}) /\
      S {t: let: (#, %, %) := periodic C $ "n" $ ("Fs" $ "n") in: #0} ->
      A
    ) ->
    (
      (when-self /\ S {t: "Fs" $ "n"}) =>> eventuallyp^ when-on["n"] A
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
      when-self /\
      S {t: "Fs" $ "n"} /\
      ("Fs'" $ "n", "Fors", "Fois") = periodic C $ "n" $ ("Fs" $ "n") ->
      A
    ) ->
    (
      correct "n" ->
      (when-self -> S {t: "Fs" $ "n"}) =>>
      always eventually A
    )
  }.
Proof.
Admitted. (* TODO *)

Lemma DPWhenTopRequestSelf C ctx :
  ctx |- C, {A:
    forall: "e":
    when[]-> "e" =>> when-self
  }.
Proof.
Admitted. (* TODO *)
