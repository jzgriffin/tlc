Require Import TLC.Syntax.Expression.
Require Import TLC.Typing.Interface.
Require Import TLC.Typing.Type.
Require Import TLC.Typing.Variant.
Require Import Coq.Lists.List.
Require TLC.Syntax.Component.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Type of individual typing components *)
Record component P : Type :=
  Component {
    syntactic_component : TLC.Syntax.Component.component P;
    (* Basic types and values *)
    ir_event : type;
    oi_event : type;
    sub_interfaces : interfaces;
    state : type;
    (* Derived types and values *)
    or_events := map fst sub_interfaces;
    ii_events := map snd sub_interfaces;
    or_event := TVariant or_events;
    ii_event := TVariant ii_events;
    event : type := ir_event + oi_event + or_event + ii_event + TPEvent;
    states : type := TNode -> state;
    output : type := state * TList or_event * TList oi_event;
    (* Function types *)
    TInitialize : type := TNode -> state;
    TRequest : type := TNode -> state -> ir_event -> output;
    TIndication : type := TNode -> state -> ii_event -> output;
    TPeriodic : type := TNode -> state -> output;
  }.
