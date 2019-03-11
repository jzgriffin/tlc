Require Import mathcomp.ssreflect.seq.
Require Import mathcomp.ssreflect.ssreflect.
Require Import tlc.logic.context.
Require Import tlc.logic.derives.
Require Import tlc.semantics.all_semantics.
Require Import tlc.syntax.all_syntax.
Require Import tlc.utility.partial_map.
Require Import tlc.utility.result.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Lemmas about predicates *)

Lemma DAPEqualSymmetric C ctx :
  ctx |- C, {A:
    forall: "tl", "tr":
    "tl" = "tr" <-> "tr" = "tl"
  }.
Proof.
Admitted. (* TODO *)

Lemma DAPInConcat C ctx :
  ctx |- C, {A:
    forall: "tsl", "tsr", "t":
    "t" \in "tsl" \/ "t" \in "tsr" ->
    "t" \in "tsl" ++ "tsr"
  }.
Proof.
Admitted. (* TODO *)

Lemma DAPInUnion C ctx :
  ctx |- C, {A:
    forall: "tsl", "tsr", "t":
    "t" \in "tsl" \/ "t" \in "tsr" ->
    "t" \in "tsl" \union "tsr"
  }.
Proof.
Admitted. (* TODO *)

Lemma DAPInMap C ctx t ts tf tft :
  ctx |- C, {A: t \in ts} ->
  [[t tf $ t]] = Success tft ->
  ctx |- C, {A: tft \in tf <$> ts}.
Proof.
Admitted. (* TODO *)

Lemma DAPConcatIn C ctx :
  ctx |- C, {A:
    forall: "t", "ts":
    "t" \in "ts" <->
    exists: "tsl": exists: "tsr": "ts" = "tsl" ++ ["t"] ++ "tsr"
  }.
Proof.
Admitted. (* TODO *)
