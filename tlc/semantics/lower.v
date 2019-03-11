(* TLC in Coq
 *
 * Module: tlc.semantics.lower
 * Purpose: Contains the assertion lowering transformation.
 *)

Require Import mathcomp.ssreflect.ssreflect.
Require Import tlc.semantics.push.
Require Import tlc.semantics.restrict.
Require Import tlc.syntax.all_syntax.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Implements component lowering by first pushing an assertion then
 * restricting it.
 *)
Definition lower_assertion (i : nat) A (TI : top_invariant A) :=
  restrict_assertion {A: "Fd" <<< [i]}
    (projT1 (push_assertion i (location_invariant_assertion TI))).
