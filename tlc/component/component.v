Require Import mathcomp.ssreflect.ssreflect.
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
  }.
