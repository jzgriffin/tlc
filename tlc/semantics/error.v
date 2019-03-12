(* TLC in Coq
 *
 * Module: tlc.semantics.error
 * Purpose: Contains the error type.
 *)

Require Import tlc.syntax.pattern.
Require Import tlc.syntax.term.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Kinds of errors produced during semantic operations
 * This type is typically used as the error type for the result monad in
 * semantic operations.
 *)
Inductive error :=
(* Opening *)
| EParameter (t : term)
(* Pattern matching *)
| EPattern (p : pattern) (t : term)
| EMatch (ta : term) (cs : cases)
(* Evaluation *)
| EFailure
| EBoolean (t : term)
| ENatural (t : term)
| EList (t : term)
| EFuel (t : term).
