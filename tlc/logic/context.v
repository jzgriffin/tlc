(* TLC in Coq
 *
 * Module: tlc.logic.context
 * Purpose: Contains the context type for syntactic proofs.
 *)

Require Import mathcomp.ssreflect.seq.
Require Import mathcomp.ssreflect.ssreflect.
Require Import tlc.semantics.all_semantics.
Require Import tlc.syntax.all_syntax.
Require Import tlc.utility.partial_map.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Logical context of bound variables *)
Definition context_variables := seq variable.

(* Logical context of assumed assertions *)
Definition context_assertions := seq assertion.

(* Logical proof context *)
Record context :=
  Context {
    context_delta : context_variables;
    context_gamma : context_assertions;
  }.

(* Context coercions *)
Coercion context_delta : context >-> context_variables.
Coercion context_gamma : context >-> context_assertions.

(* Produces a term equivalents map from a context
 * All premises of the form "tl = tr" appear in the equivalents map.
 *)
Fixpoint context_equivalences (Gamma : context_assertions) : equivalents :=
  match Gamma with
  | [::] => [::]
  | A :: Gamma =>
    let e := context_equivalences Gamma in
    if A is APredicate (PEqual tl tr) then e{= tl := tr} else e
  end.
