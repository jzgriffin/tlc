(* TLC in Coq
 *
 * Module: tlc.semantics.error
 * Purpose: Contains the error type.
 *)

Require Import mathcomp.ssreflect.seq.
Require Import mathcomp.ssreflect.ssreflect.
Require Import tlc.semantics.pattern.
Require Import tlc.syntax.all_syntax.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Errors that may be encountered while operating on terms and assertions *)
Inductive error :=
| EFuel (t : term)
| EEmptyMatch (a : term)
| EMatch (p : pattern) (pe : pattern_error) (a : term) (e : error)
| EOpenTerm (t : term) (us : seq term) (k : nat) (x : parameter)
| EOpenAssertion (A : assertion) (us : seq term) (k : nat) (x : parameter).
