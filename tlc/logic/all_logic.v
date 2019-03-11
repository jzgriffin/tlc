(* TLC in Coq
 *
 * Module: tlc.logic.all_logic
 * Purpose: Exports the entire logic module by exporting all submodules.
 *
 * The logic module contains the logic of TLC.  The logic is defined in terms
 * of the derives type, which is an inductive type containing the axioms of
 * TLC: those of the sequent logic, temporal logic, and program logic.  This
 * type forms a proof system for TLC, on top of which derived rules and lemmas
 * may be described.  Those derived rules and lemmas are defined in the
 * predicate, program, sequent, and temporal submodules.
 *)

Require Export tlc.logic.context.
Require Export tlc.logic.derives.
Require Export tlc.logic.predicate.
Require Export tlc.logic.program.
Require Export tlc.logic.sequent.
Require Export tlc.logic.temporal.
