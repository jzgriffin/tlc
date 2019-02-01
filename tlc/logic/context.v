Require Import mathcomp.ssreflect.seq.
Require Import mathcomp.ssreflect.ssreflect.
Require Import tlc.assert.all_assert.
Require Import tlc.compute.all_compute.
Require Import tlc.utility.partial_map.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Logical context of assertions *)
Definition context := seq assertion.

(* Produces an evaluation environment from a context *)
(* All expression hypotheses of the form "$v = e" appear in the environment *)
Fixpoint context_environment (C : context) : environment :=
  match C with
  | [::] => [::]
  | A :: C =>
    if A is {A: {e: $v = e}} then (context_environment C){= v := e}
    else context_environment C
  end.
