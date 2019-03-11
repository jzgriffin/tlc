(* TLC in Coq
 *
 * Module: tlc.operation.all_operation
 * Purpose: Exports the entire operation module by exporting all submodules.
 *
 * The operation module contains definitions used in the basic operation of
 * TLC.  Currently, this comprises the orientation and periodic event types,
 * which appear both in the operational semantics and the logic itself.
 *)

Require Export tlc.operation.orientation.
Require Export tlc.operation.periodic_event.
