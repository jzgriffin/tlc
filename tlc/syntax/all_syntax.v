(* TLC in Coq
 *
 * Module: tlc.syntax.all_syntax
 * Purpose: Exports the entire syntax module by exporting all submodules.
 *
 * The syntax module contains the types that define the syntactic structures
 * of TLC as well as any notations that are helpful in constructing Coq terms
 * for those structures.  For example, the term submodule defines the syntax
 * of the term language.
 *
 * This module only defines the syntax of these structures; specific meaning
 * is given to them by the semantics module.
 *)

Require Export tlc.syntax.assertion.
Require Export tlc.syntax.constructor.
Require Export tlc.syntax.function.
Require Export tlc.syntax.literal.
Require Export tlc.syntax.parameter.
Require Export tlc.syntax.pattern.
Require Export tlc.syntax.predicate.
Require Export tlc.syntax.term.
Require Export tlc.syntax.variable.
