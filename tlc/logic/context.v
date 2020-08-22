(* TLC in Coq
 *
 * Module: tlc.logic.context
 * Purpose: Contains the context type for syntactic proofs.
 *)

Require Import mathcomp.ssreflect.seq.
Require Import mathcomp.ssreflect.ssreflect.
Require Import tlc.semantics.all_semantics.
Require Import tlc.syntax.all_syntax.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Logical context of bound rigid variables *)
Definition context_bindings := seq rigid.

(* Logical context of assumed assertions *)
Definition context_assumptions := seq assertion.

(* Logical proof context *)
Record context :=
  Context {
    context_delta : context_bindings;
    context_gamma : context_assumptions;
  }.

(* Context coercions *)
Coercion context_delta : context >-> context_bindings.
Coercion context_gamma : context >-> context_assumptions.

(* A context with no bound variables or assumptions *)
Notation Z0 := (Context [::] [::]).

(* Compute the set of rigid variables appearing in a context *)
Definition context_rigids Z :=
  foldr (fun A xs => assertion_rigids A ++ xs)
    (context_delta Z) (context_gamma Z).
