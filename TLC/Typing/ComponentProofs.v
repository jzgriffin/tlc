Require Import TLC.Syntax.Expression.
Require Import TLC.Typing.Component.
Require Import TLC.Typing.Expression.
Require Import TLC.Typing.Interface.
Require Import TLC.Typing.Type.
Require Import TLC.Typing.Variant.
Require Import Coq.Lists.List.
Require TLC.Syntax.Component.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module SC := TLC.Syntax.Component.

(* Proofs for a typing component *)
Record component_proofs {P} (C : component P) : Type :=
  ComponentProofs {
    initialize_type : nil |-e
      ^(SC.initialize (syntactic_component C)) : (TInitialize C) | C;
    request_type : nil |-e
      ^(SC.request (syntactic_component C)) : (TRequest C) | C;
    indication_type : nil |-e
      ^(SC.indication (syntactic_component C)) : (TIndication C) | C;
    periodic_type : nil |-e
      ^(SC.periodic (syntactic_component C)) : (TPeriodic C) | C;
  }.

(*
(* Event constructor functions *)
Definition event_ir' {N} ir : expression N := ^CLeft <- ^CLeft <- ^CLeft <- ^CLeft <- ir.
Definition event_ir {G C} (ir : {e : expression (length G) & G |-e e ~ @ir_event C}) : G |-e (event_ir' (projT1 ir)) ~ @event C.
Proof.
  repeat econstructor.
  apply (projT2 ir).
Defined.
Print event_ir.

Definition event_ir C ir : event C := inl (inl (inl (inl ir))).
Definition event_oi C oi : event C := inl (inl (inl (inr oi))).
Definition event_or C or : event C := inl (inl (inr or)).
Definition event_ii C ii : event C := inl (inr ii).
Definition event_p C p : event C := inr p.
*)
