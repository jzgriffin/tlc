(* TLC in Coq
 *
 * Module: tlc.component.component
 * Purpose: Contains the component type.
 *
 * The component type corresponds to the Comp type in TLC.  However, with the
 * untyped nature of this implementation, the typing information is removed.
 * Instead, each component comprises only terms defining the initialization,
 * request processing, indication processing, and periodic processing
 * functions.  In TLC, these functions are named init, request, indication,
 * and periodic.
 *)

Require Import mathcomp.ssreflect.seq.
Require Import mathcomp.ssreflect.ssrbool.
Require Import mathcomp.ssreflect.ssreflect.
Require Import tlc.semantics.term.
Require Import tlc.syntax.all_syntax.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Record component :=
  Component {
    (* output := state * seq or_event * seq oi_event *)
    initialize : term; (* node -> state *)
    request : term; (* node -> state -> ir_event -> output *)
    indication : term; (* node -> state -> ii_event -> output *)
    periodic : term; (* node -> state -> output *)
    initialize_computable : term_computable initialize;
    request_computable : term_computable request;
    indication_computable : term_computable indication;
    periodic_computable : term_computable periodic;
  }.

(* Hints *)
Hint Resolve initialize_computable : core.
Hint Resolve request_computable : core.
Hint Resolve indication_computable : core.
Hint Resolve periodic_computable : core.
