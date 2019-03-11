(* TLC in Coq
 *
 * Module: tlc.semantics.restrict
 * Purpose: Contains the assertion restricting algorithm.
 *)

Require Import mathcomp.ssreflect.ssreflect.
Require Import tlc.syntax.assertion.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Restricts an assertion to remain valid on traces that are extended with
 * interleaving events
 *
 * NOTE: This algorithm is slightly different from the algorithm in TLC.  The
 * true algorithm operates on a subset of assertions.  This algorithm operates
 * on all assertions, but returns false when an illegal assertion is given.
 *)
Fixpoint restrict_assertion A' A :=
  match A with
  | APredicate _ => A
  | ANot A => {A: ~restrict_assertion A' A}
  | AAnd Al Ar => {A: restrict_assertion A' Al /\ restrict_assertion A' Ar}
  | AForAll v A => {A: forall: v: restrict_assertion A' A}
  | AAlways' A => {A: always^ (A' -> restrict_assertion A' A)}
  | AAlwaysP' A => {A: alwaysp^ (A' -> restrict_assertion A' A)}
  | AEventually' A => {A: eventually^ (restrict_assertion A' A)}
  | AEventuallyP' A => {A: eventuallyp^ (restrict_assertion A' A)}
  | ANext _ => AFalse (* Illegal restrict *)
  | APrevious _ => AFalse (* Illegal restrict *)
  | ASelf _ => AFalse (* Illegal restrict *)
  end.
