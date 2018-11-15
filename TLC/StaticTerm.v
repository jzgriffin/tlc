Require Import TLC.Component.
Require Import TLC.Event.
Require Import TLC.Flexible.
Require Import TLC.Orientation.
Require Import TLC.Term.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Static/non-temporal terms *)
Inductive static_term {C} : forall T, term C T -> Type :=
| StaticFlexible T (x : flexible C T) :
  static_term (Flexible x)
| StaticValue T (x : T) :
  static_term (Value x)
| StaticApplication D R (f : term C (D -> R)) (x : term C D) :
  static_term f ->
  static_term x ->
  static_term (Application f x)
| StaticNot (A : term C Prop) :
  static_term A ->
  static_term (Not A)
| StaticAnd (A1 A2 : term C Prop) :
  static_term A1 ->
  static_term A2 ->
  static_term (And A1 A2)
| StaticOr (A1 A2 : term C Prop) :
  static_term A1 ->
  static_term A2 ->
  static_term (Or A1 A2)
| StaticIf (A1 A2 : term C Prop) :
  static_term A1 ->
  static_term A2 ->
  static_term (If A1 A2)
| StaticForAll T (A : T -> term C Prop) :
  (forall x, static_term (A x)) ->
  static_term (ForAll A)
| StaticExists T (A : T -> term C Prop) :
  (forall x, static_term (A x)) ->
  static_term (Exists A)
| StaticEquals T (x y : term C T) :
  static_term x ->
  static_term y ->
  static_term (Equals x y)
| StaticNodeSet :
  static_term NodeSet
| StaticCorrectSet :
  static_term CorrectSet
| StaticCorrect :
  static_term Correct.

Fixpoint denote_static_term {C} (fd : flexible_denotation C)
  T (t : term C T) (st : static_term t) : T :=
  match st with
  | StaticFlexible x => fd _ x
  | StaticValue x => x
  | StaticApplication f x => (denote_static_term fd f) (denote_static_term fd x)
  | StaticEquals x y => denote_static_term fd x = denote_static_term fd y
  | StaticNot A => ~denote_static_term fd A
  | StaticAnd A1 A2 => denote_static_term fd A1 /\ denote_static_term fd A2
  | StaticOr A1 A2 => denote_static_term fd A1 \/ denote_static_term fd A2
  | StaticIf A1 A2 => denote_static_term fd A1 -> denote_static_term fd A2
  | StaticForAll A => forall x, denote_static_term fd (A x)
  | StaticExists A => exists x, denote_static_term fd (A x)
  | StaticNodeSet => List.nil
  | StaticCorrectSet => List.nil
  | StaticCorrect => fun _ => False
  end.
