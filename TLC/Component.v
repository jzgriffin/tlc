Require Import Coq.Vectors.Vector.
Require Import TLC.Variant.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition interface : Type := Type * Type.
Definition interfaces := {n : nat & Vector.t interface n}.

Record component :=
  Component {
    node : Type;
    message : Type;
    ir_event : Type;
    oi_event : Type;
    sub_interfaces : interfaces;
    or_events := Vector.map fst (projT2 sub_interfaces);
    ii_events := Vector.map snd (projT2 sub_interfaces);
    or_event := variant or_events;
    ii_event := variant ii_events;
    state : Type;
    output : Type := state * list or_event * list oi_event;
    initialize : node -> state;
    request : node -> state -> ir_event -> output;
    indication : node -> state -> ii_event -> output;
    periodic : node -> state -> output;
  }.

Arguments initialize : clear implicits.
Arguments request : clear implicits.
Arguments indication : clear implicits.
Arguments periodic : clear implicits.

Definition states C := node C -> state C.
Definition sub_index C := Fin.t (projT1 (sub_interfaces C)).
