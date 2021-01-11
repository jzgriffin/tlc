(* TLC in Coq
 *
 * Module: tlc.component.all_component
 * Purpose: Exports the entire component module by exporting all submodules.
 *
 * The component module contains the functional implementations and
 * logical specifications of all distributed components except the fair loss
 * link.  The fair loss link is defined in the operational semantics of TLC.
 * The components implemented in this module are defined in terms of the fair
 * loss link.  Each component-defining submodule in this module exports a
 * component definition (typically named after the module) and a set of
 * theorems about that component, as well as any supporting lemmas necessary
 * to prove the theorems.
 *)

Require Export tlc.component.component.
Require Export tlc.component.perfect_link_spec.
Require Export tlc.component.stubborn_link_spec.
