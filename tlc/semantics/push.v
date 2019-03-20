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
Fixpoint push_assertion (i : nat) A (TA : top_assertion A) : assertion.
Proof.
  inversion TA; subst.
  - set d'i := rcons d' i.
    set td'i := TList [seq TLiteral (LNatural n) | n <- d'i].
    by exact: {A: on tn, ("Fd" = td'i /\ "Fo" = to /\ "Fe" = te)}.
  - by exact: {A: correct tn}.
  - by exact: {A: ~(push_assertion i _ X)}.
  - by exact: {A: (push_assertion i _ X) /\ (push_assertion i _ X0)}.
  - by exact: {A: forall: v: (push_assertion i _ X)}.
  - by exact: {A: always^ (push_assertion i _ X)}.
  - by exact: {A: alwaysp^ (push_assertion i _ X)}.
  - by exact: {A: eventually^ (push_assertion i _ X)}.
  - by exact: {A: eventuallyp^ (push_assertion i _ X)}.
Defined.
