(* TLC in Coq
 *
 * Module: tlc.utility.function
 * Purpose: Contains helpers for functional programming.
 *)

Require Import mathcomp.ssreflect.ssreflect.
Require Import mathcomp.ssreflect.ssrnat.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Iterate f over x n times *)
Fixpoint iter A (f : A -> A) (x : A) n :=
  match n with
  | 0 => x
  | n.+1 => iter f (f x) n
  end.
