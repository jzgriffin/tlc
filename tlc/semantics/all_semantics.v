(* TLC in Coq
 *
 * Module: tlc.semantics.all_semantics
 * Purpose: Exports the entire semantics module by exporting all submodules.
 *
 * The semantics module contains types and functions pertaining to the
 * semantics of terms and assertions within the TLC language.  While the
 * syntax module only contains definitions of the syntactic structures of
 * terms and assertions, this module provides semantics for those structures.
 *
 * Submodules containing the semantics for a particular syntactic structure
 * are given the same name as the corresponding syntax submodule.  For
 * example, the term submodule contains semantics for the term syntactic
 * structure.
 *)

Require Export tlc.semantics.assertion.
Require Export tlc.semantics.constructor.
Require Export tlc.semantics.error.
Require Export tlc.semantics.lower.
Require Export tlc.semantics.pattern.
Require Export tlc.semantics.predicate.
Require Export tlc.semantics.tactics.
Require Export tlc.semantics.term.
