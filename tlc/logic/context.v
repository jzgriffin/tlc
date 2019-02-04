Require Import mathcomp.ssreflect.seq.
Require Import mathcomp.ssreflect.ssreflect.
Require Import tlc.semantics.all_semantics.
Require Import tlc.syntax.all_syntax.
Require Import tlc.utility.partial_map.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Logical context of assertions *)
Definition context := seq assertion.

(* Produces an evaluation environment from a context
 * All term hypotheses of the form "v = t" appear in the environment
 *)
Fixpoint context_environment (C : context) : environment :=
  match C with
  | [::] => [::]
  | A :: C =>
    if A is {t: TVariable v = t} then (context_environment C){= v := t}
    else context_environment C
  end.
