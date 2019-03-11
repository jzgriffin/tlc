(* TLC in Coq
 *
 * Module: tlc.semantics.equivalents
 * Purpose: Contains the equivalents type.
 *)

Require Import mathcomp.ssreflect.eqtype.
Require Import mathcomp.ssreflect.ssrbool.
Require Import mathcomp.ssreflect.ssreflect.
Require Import tlc.syntax.term.
Require Import tlc.utility.partial_map.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Partial mapping from terms to terms *)
Definition equivalents := partial_map [eqType of term] term.
