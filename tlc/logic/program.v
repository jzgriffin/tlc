Require Import mathcomp.ssreflect.ssreflect.
Require Import tlc.component.component.
Require Import tlc.logic.derives.
Require Import tlc.operation.periodic_event.
Require Import tlc.semantics.all_semantics.
Require Import tlc.syntax.all_syntax.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Derived program rules and lemmas *)

Lemma DPIROI C Gamma (S : term -> assertion) tn te te' :
  Gamma |- C, {A:
    S "s" /\
      te' \in {t: let: (%, %, #) := request C $ tn $ "s" $ te in: #0}
  } ->
  Gamma |- C, {A:
    when-on[tn] when[]-> te /\ S {t: "Fs" $ tn} =>>
    eventually when-on[tn] when[]<- te'
  }.
Proof.
Admitted. (* TODO *)

Lemma DPIIOI C Gamma (S : term -> assertion) tn ti te te' :
  Gamma |- C, {A:
    S "s" /\
      te' \in {t: let: (%, %, #) := indication C $ tn $ "s" $ (ti, te) in: #0}
  } ->
  Gamma |- C, {A:
    when-on[tn] when[ti]<- te /\ S {t: "Fs" $ tn} =>>
    eventually^ when-on[tn] when[]<- te'
  }.
Proof.
Admitted. (* TODO *)

Lemma DPInvL C Gamma A :
  non_temporal_assertion A ->
  Gamma |- C, {A:
    forall: "e",
    when[]-> "e" /\
    request C $ "Fn" $ ("Fs" $ "Fn") $ "e" = ("Fs'" $ "Fn", "Fors", "Fois") ->
    A
  } ->
  Gamma |- C, {A:
    forall: "i", forall: "e",
    when["i"]<- "e" /\
    indication C $ "Fn" $ ("Fs" $ "Fn") $ ("i", "e") =
      ("Fs'" $ "Fn", "Fors", "Fois") ->
    A
  } ->
  Gamma |- C, {A:
    when[]~> PE /\
    periodic C $ "Fn" $ ("Fs" $ "Fn") = ("Fs'" $ "Fn", "Fors", "Fois") ->
    A
  } ->
  Gamma |- C, {A: when-self =>> A}.
Proof.
Admitted. (* TODO *)

Lemma DPInvS'' C Gamma (S : term -> assertion) tn :
  Gamma |- C, {A:
    forall: "s", forall: "e",
    S "s" ->
    S {t: let: (#, %, %) := request C $ tn $ "s" $ "e" in: #0}
  } ->
  Gamma |- C, {A:
    forall: "s", forall: "i", forall: "e",
    S "s" ->
    S {t: let: (#, %, %) := indication C $ tn $ "s" $ ("i", "e") in: #0}
  } ->
  Gamma |- C, {A:
    forall: "s",
    S "s" ->
    S {t: let: (#, %, %) := periodic C $ tn $ "s" in: #0}
  } ->
  Gamma |- C, {A:
    (when-self /\ S {t: "Fs'" $ tn}) =>>
    always^ (when-self -> S {t: "Fs" $ tn})
  }.
Proof.
Admitted. (* TODO *)

Lemma DPAPerSA C Gamma (S : term -> assertion) tn A :
  non_temporal_assertion A ->
  Gamma |- C, {A:
    "Fn" = tn /\
    when-self /\
    S {t: "Fs" $ tn} /\
    ("Fs'" $ tn, "Fors", "Fois") = periodic C $ tn $ ("Fs" $ tn) ->
    A
  } ->
  Gamma |- C, {A:
    correct tn ->
    (when-self -> S {t: "Fs" $ tn}) =>>
    always eventually A
  }.
Proof.
Admitted. (* TODO *)
