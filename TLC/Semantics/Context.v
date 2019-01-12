Require Import TLC.Parameters.
Require Import TLC.Semantics.Type.
Require Import TLC.Typing.Context.
Require Import TLC.Utility.HList.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section denote_context.

  Variable P : parameters.

  (* Denotation of a typing context *)
  Definition context_denotation (G : context) := hlist (denote_type P) G.

End denote_context.

(* Notation scope for typing contexts *)
Bind Scope hlist_scope with context_denotation.

(* Notations for denoting typing contexts *)
Notation "[G: x | y ]" := (context_denotation y x) (at level 0) : type_scope.
