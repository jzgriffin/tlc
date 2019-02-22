Require Import mathcomp.ssreflect.ssreflect.
Require Import tlc.logic.derives.
Require Import tlc.semantics.all_semantics.
Require Import tlc.syntax.all_syntax.
Require Import tlc.utility.result.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Lemmas about predicates *)

Lemma DInConcat C Gamma tsl tsr t :
  Gamma |- C, {A: t \in tsl \/ t \in tsr} ->
  Gamma |- C, {A: t \in tsl ++ tsr}.
Proof.
Admitted. (* TODO *)

Lemma DInUnion C Gamma tsl tsr t :
  Gamma |- C, {A: t \in tsl \/ t \in tsr} ->
  Gamma |- C, {A: t \in tsl \union tsr}.
Proof.
Admitted. (* TODO *)

Lemma DInMap C Gamma t ts tf tft :
  Gamma |- C, {A: t \in ts} ->
  [[t tf $ t]] = Success tft ->
  Gamma |- C, {A: tft \in tf <$> ts}.
Proof.
Admitted. (* TODO *)

Lemma DConcatIn Gamma C t ts :
  Gamma |- C, {A:
    t \in ts <-> exists: "tsl", exists: "tsr", ts = "tsl" ++ [t] ++ "tsr"
  }.
Proof.
Admitted. (* TODO *)
