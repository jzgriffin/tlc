Require Import mathcomp.ssreflect.ssreflect.
Require Import tlc.logic.derives.
Require Import tlc.syntax.all_syntax.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Lemmas about predicates *)

Lemma DInUnion C Gamma tsl tsr t :
  Gamma |- C, {A: t \in tsl \/ t \in tsr} ->
  Gamma |- C, {A: t \in tsl \union tsr}.
Proof.
Admitted. (* TODO *)
