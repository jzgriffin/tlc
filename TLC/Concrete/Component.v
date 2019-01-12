Require Import TLC.Concrete.Interface.
Require Import TLC.Concrete.PEvent.
Require Import TLC.Parameters.
Require Import TLC.Utility.Variant.
Require Import Coq.Lists.List.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Type of individual concrete components *)
Record component {P} : Type :=
  Component {
    (* Basic types and values *)
    ir_event : Type;
    oi_event : Type;
    sub_interfaces : interfaces;
    state : Type;
    (* Derived types and values *)
    or_events := map fst sub_interfaces;
    ii_events := map snd sub_interfaces;
    or_event := variant or_events;
    ii_event := variant ii_events;
    event : Type := ir_event + oi_event + or_event + ii_event + p_event;
    states : Type := node P -> state;
    output : Type := state * list or_event * list oi_event;
    (* Functions *)
    initialize : node P -> state;
    request : node P -> state -> ir_event -> output;
    indication : node P -> state -> ii_event -> output;
    periodic : node P -> state -> output;
  }.

Arguments component : clear implicits.

(* Event constructor functions *)
Definition event_ir {P} (C : component P) ir : event C :=
  inl (inl (inl (inl ir))).
Definition event_oi {P} (C : component P) oi : event C :=
  inl (inl (inl (inr oi))).
Definition event_or {P} (C : component P) or : event C :=
  inl (inl (inr or)).
Definition event_ii {P} (C : component P) ii : event C :=
  inl (inr ii).
Definition event_p {P} (C : component P) p : event C :=
  inr p.
