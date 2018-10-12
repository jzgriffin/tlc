From mathcomp.ssreflect
Require Import ssreflect eqtype seq.
From tlc.utility
Require Import variant.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Record component :=
  Component {
    node : eqType;
    message : eqType;
    ir_event : eqType;
    oi_event : eqType;
    or_ii_events : seq (eqType * eqType)%type;
    or_events := map fst or_ii_events;
    ii_events := map snd or_ii_events;
    or_event := eqVariant or_events;
    ii_event := eqVariant ii_events;
    state : eqType;
    output := (state * (seq or_event) * (seq oi_event))%type;
    init : node -> state;
    request : node -> state -> ir_event -> output;
    indication : node -> state -> ii_event -> output;
    periodic : node -> state -> output;
  }.
