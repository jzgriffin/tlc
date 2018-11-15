Require Import TLC.Component.
Require Import TLC.Event.
Require Import TLC.Location.
Require Import TLC.Orientation.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Inductive flexible {C} : Type -> Type :=
| Fn : flexible (node C)
| Fd : flexible (location C)
| Fo : flexible orientation
| Fe : flexible (event C)
| Fors : flexible (list (or_event C))
| Fois : flexible (list (oi_event C))
| Fs : flexible (states C)
| Fs' : flexible (states C).

Arguments flexible : clear implicits.

Definition flexible_denotation C : Type :=
  forall T, flexible C T -> T.
