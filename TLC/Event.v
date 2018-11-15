Require Import TLC.Component.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Inductive p_event {C : component} : Type := per.

Arguments p_event : clear implicits.

Inductive event {C} : Type :=
| IREvent (e : ir_event C)
| OIEvent (e : oi_event C)
| OREvent (e : or_event C)
| IIEvent (e : ii_event C)
| PEvent (e : p_event C).

Arguments event : clear implicits.

Coercion IREvent : ir_event >-> event.
Coercion OIEvent : oi_event >-> event.
Coercion OREvent : or_event >-> event.
Coercion IIEvent : ii_event >-> event.
Coercion PEvent : p_event >-> event.
