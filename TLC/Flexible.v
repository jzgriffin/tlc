Require Import Coq.Program.Equality.
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

Definition flexible_eqb {C} T (x y : flexible C T) : bool :=
  match x, y with
  | Fn, Fn => true
  | Fd, Fd => true
  | Fo, Fo => true
  | Fe, Fe => true
  | Fors, Fors => true
  | Fois, Fois => true
  | Fs, Fs => true
  | Fs', Fs' => true
  | _, _ => false
  end.

Lemma flexible_eq_dec {C} T (x y : flexible C T) : {x = y} + {x <> y}.
Proof.
  dependent induction x; dependent destruction y;
  try now left; try now right.
Admitted. (* TODO *)

Definition flexible_denotation C : Type :=
  forall T, flexible C T -> T.
