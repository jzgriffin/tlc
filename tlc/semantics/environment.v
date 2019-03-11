(* TLC in Coq
 *
 * Module: tlc.semantics.environment
 * Purpose: Contains the environment type.
 *)

Require Import mathcomp.ssreflect.eqtype.
Require Import mathcomp.ssreflect.seq.
Require Import mathcomp.ssreflect.ssrbool.
Require Import mathcomp.ssreflect.ssreflect.
Require Import tlc.semantics.equivalents.
Require Import tlc.syntax.term.
Require Import tlc.syntax.variable.
Require Import tlc.utility.partial_map.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Partial mapping from variables to terms *)
Definition environment := partial_map [eqType of variable] term.

(* Produces an equivalents map for an environment *)
Definition environment_equivalents (e : environment) :=
  map (fun '(v, t) => (TVariable v, t)) e.
