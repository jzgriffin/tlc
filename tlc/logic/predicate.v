(* TLC in Coq
 *
 * Module: tlc.logic.predicate
 * Purpose: Contains derived rules and lemmas regarding predicates.
 *)

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

(* The equality predicate is symmetric *)
Lemma DAPEqualSymmetric C ctx :
  ctx |- C, {A:
    forall: "tl", "tr":
    "tl" = "tr" <-> "tr" = "tl"
  }.
Proof.
Admitted. (* TODO *)

(* No element may appear in an empty list *)
Lemma DAPInNil C ctx :
  ctx |- C, {A:
    forall: "t":
    ~("t" \in [])
  }.
Proof.
Admitted. (* TODO *)

(* If t is in tsl or tsr, then t is in the concatenation of tsl and tsr *)
Lemma DAPInConcat C ctx :
  ctx |- C, {A:
    forall: "tsl", "tsr", "t":
    "t" \in "tsl" \/ "t" \in "tsr" ->
    "t" \in "tsl" ++ "tsr"
  }.
Proof.
Admitted. (* TODO *)

(* If t is in tsl or tsr, then t is in the union of tsl and tsr *)
Lemma DAPInUnion C ctx :
  ctx |- C, {A:
    forall: "tsl", "tsr", "t":
    "t" \in "tsl" \/ "t" \in "tsr" ->
    "t" \in "tsl" \union "tsr"
  }.
Proof.
Admitted. (* TODO *)

(* If t is in ts, then t under mapping tf is in tf mapped over ts *)
Lemma DAPInMap C ctx t ts tf tft :
  ctx |- C, {A: t \in ts} ->
  [[t tf $ t]] = Success tft ->
  ctx |- C, {A: tft \in tf <$> ts}.
Proof.
Admitted. (* TODO *)

(* t is in ts if and only if there exist two lists tsl and tsr such that ts is
 * equal to the concatenation of tsl, t, and tsr
 *)
Lemma DAPConcatIn C ctx :
  ctx |- C, {A:
    forall: "t", "ts":
    "t" \in "ts" <->
    exists: "tsl": exists: "tsr": "ts" = "tsl" ++ ["t"] ++ "tsr"
  }.
Proof.
Admitted. (* TODO *)
