(* TLC in Coq
 *
 * Module: tlc.semantics.push
 * Purpose: Contains the assertion pushing algorithm.
 *)

Require Import mathcomp.ssreflect.eqtype.
Require Import mathcomp.ssreflect.seq.
Require Import mathcomp.ssreflect.ssrbool.
Require Import mathcomp.ssreflect.ssreflect.
Require Import mathcomp.ssreflect.ssrnat.
Require Import tlc.syntax.all_syntax.
Require Import tlc.utility.seq.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Pushes an assertion from the top to a lower layer i
 * TODO: Consider rewriting this in Gallina using the convoy pattern.
 *)
Definition push_assertion (i : nat) A (TA : top_assertion A) : assertion.
Proof.
  elim: TA => [d tn dp to te | d tn | d A0 _ A0' | d Al Ar _ Al' _ Ar'
    | d v A0 _ A0' | d A0 _ A0' | d A0 _ A0' | d A0 _ A0' | d A0 _ A0'].
  - set d' := rcons dp i.
    set td' := TList [seq TLiteral (LNatural n) | n <- d'].
    by exact: {A: on tn, ("Fd" = td' /\ "Fo" = to /\ "Fe" = te)}.
  - by exact: {A: correct tn}.
  - by exact: {A: ~A0'}.
  - by exact: {A: Al' /\ Ar'}.
  - by exact: {A: forall: v: A0'}.
  - by exact: {A: always^ A0'}.
  - by exact: {A: alwaysp^ A0'}.
  - by exact: {A: eventually^ A0'}.
  - by exact: {A: eventuallyp^ A0'}.
Defined.
