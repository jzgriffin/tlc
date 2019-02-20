Require Import mathcomp.ssreflect.ssreflect.
Require Import tlc.component.component.
Require Import tlc.logic.derives.
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
