Require Import Coq.Lists.List.
Require Import Coq.Vectors.Vector.
Require Import TLC.Component.
Require Import TLC.Event.
Require Import TLC.Flexible.
Require Import TLC.Orientation.
Require Import TLC.Variant.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Terms of the assertion language *)
Inductive term {C} : Type -> Type :=
| Flexible T (x : flexible C T) : term T
| Value T (x : T) : term T
| Application D R (f : term (D -> R)) (x : term D) : term R
(* First-order logic *)
| Not (A : term Prop) : term Prop
| And (A1 A2 : term Prop) : term Prop
| Or (A1 A2 : term Prop) : term Prop
| If (A1 A2 : term Prop) : term Prop
| ForAll T (A : T -> term Prop) : term Prop
| Exists T (A : T -> term Prop) : term Prop
(* Temporal logic *)
| Always' (A : term Prop) : term Prop
| AlwaysPast' (A : term Prop) : term Prop
| Eventually' (A : term Prop) : term Prop
| EventuallyPast' (A : term Prop) : term Prop
| Next (A : term Prop) : term Prop
| Self (A : term Prop) : term Prop
(* Special cases *)
| Equals T (x y : term T) : term Prop
| NodeSet : term (list (node C))
| CorrectSet : term (list (node C))
| Correct : term (node C -> Prop).

Arguments term : clear implicits.

Coercion Flexible : flexible >-> term.

Delimit Scope tlc_core_scope with tlc.
Bind Scope tlc_core_scope with term.

(* Notations for building terms *)
Notation "^ x" := (Value x)
  (at level 0) : tlc_core_scope.
Notation "x <- y" := (Application x y)
  (at level 10, left associativity) : tlc_core_scope.
Notation "'apply:' f x .. y" := (Application .. (Application f x) .. y)
  (at level 10, x, y at level 9) : tlc_core_scope.
Notation "~ A" := (Not A)
  : tlc_core_scope.
Notation "A1 /\ A2" := (And A1 A2)
  : tlc_core_scope.
Notation "A1 \/ A2" := (Or A1 A2)
  : tlc_core_scope.
Notation "A1 -> A2" := (If A1 A2)
  : tlc_core_scope.
Notation "'forall:' x : T , A" := (ForAll (fun x : T => A%tlc))
  (at level 65, x at level 99 as ident, A at level 200, right associativity)
  : tlc_core_scope.
Notation "'forall:' x , A" := (ForAll (fun x => A%tlc))
  (at level 65, x at level 99 as ident, A at level 200, right associativity)
  : tlc_core_scope.
Notation "'exists:' x : T , A" := (Exists (fun x : T => A%tlc))
  (at level 65, x at level 99 as ident, A at level 200, right associativity)
  : tlc_core_scope.
Notation "'exists:' x , A" := (Exists (fun x  => A%tlc))
  (at level 65, x at level 99 as ident, A at level 200, right associativity)
  : tlc_core_scope.
Notation "'always^:' A" := (Always' A)
  (at level 70, right associativity) : tlc_core_scope.
Notation "'alwaysp^:' A" := (AlwaysPast' A)
  (at level 70, right associativity) : tlc_core_scope.
Notation "'eventually^:' A" := (Eventually' A)
  (at level 70, right associativity) : tlc_core_scope.
Notation "'eventuallyp^:' A" := (EventuallyPast' A)
  (at level 70, right associativity) : tlc_core_scope.
Notation "'next:' A" := (Next A)
  (at level 70, right associativity) : tlc_core_scope.
Notation "'self:' A" := (Self A)
  (at level 70, right associativity) : tlc_core_scope.
Notation "x = y" := (Equals x y)
: tlc_core_scope.

(* Derived first-order operators *)
Definition NotEquals {C} T (x y : term C T) : term C _ := ~(x = y).
Notation "x <> y" := (NotEquals x y)
  : tlc_core_scope.
Definition Iff {C} A1 A2 : term C _ := (A1 -> A2) /\ (A2 -> A1).
Notation "A1 <-> A2" := (Iff A1 A2)
  : tlc_core_scope.

(* Derived temporal operators *)
Definition Always C A : term C _ := A /\ always^: A.
Notation "'always:' A" := (Always A)
  (at level 70, right associativity) : tlc_core_scope.
Definition AlwaysPast C A : term C _ := A /\ alwaysp^: A.
Notation "'alwaysp:' A" := (AlwaysPast A)
  (at level 70, right associativity) : tlc_core_scope.
Definition Eventually C A : term C _ := A \/ eventually^: A.
Notation "'eventually:' A" := (Eventually A)
  (at level 70, right associativity) : tlc_core_scope.
Definition EventuallyPast C A : term C _ := A \/ eventuallyp^: A.
Notation "'eventuallyp:' A" := (EventuallyPast A)
  (at level 70, right associativity) : tlc_core_scope.
Definition Entails C A A' : term C _ := always: (A -> A').
Notation "A =>> A'" := (Entails A A')
  (at level 98, right associativity) : tlc_core_scope.
Definition Congruent C A A' : term C _ := (A =>> A') /\ (A' =>> A).
Notation "A <=> A'" := (Congruent A A')
  (at level 98, right associativity) : tlc_core_scope.
Definition LeadsTo C A A' : term C _ := always: (A -> eventually: A').
Notation "A ~> A'" := (LeadsTo A A')
  (at level 97, right associativity) : tlc_core_scope.
Definition PrecededBy C A A' : term C _ := always: (A -> eventuallyp: A').
Notation "A <~ A'" := (PrecededBy A A')
  (at level 97, right associativity) : tlc_core_scope.

(* Syntactic sugar for building products *)
Notation "( x , y , .. , z )" := (^pair <- (.. (^pair <- x <- y) ..) <- z)%tlc
  : tlc_core_scope.

(* Syntactic sugar for building lists *)
Notation "[ ]" := (^List.nil)%tlc
  : tlc_core_scope.
Notation "x :: l" := (^List.cons <- x <- l)%tlc
  : tlc_core_scope.
Notation "[ x ]" := (x :: [])%tlc
  : tlc_core_scope.
Notation "[ x ; y ; .. ; z ]" :=
  (x :: (y :: (.. (^List.cons <- z <- []) ..)))%tlc
  : tlc_core_scope.

(* Syntactic sugar *)
Definition On {C} n A : term C _ := Fn = n /\ A.
Notation "'on:' n , A" := (On n A)
  (at level 65, right associativity) : tlc_core_scope.
Definition WhenTop {C} o e : term C _ := Fd = [] /\ Fo = o /\ Fe = e.
Notation "'when[]:' o , e" := (WhenTop o e)
  (at level 65, right associativity) : tlc_core_scope.
Definition WhenSub {C} i o e : term C _ := Fd = [i] /\ Fo = o /\ Fe = e.
Notation "'when:' i , o , e" := (WhenSub i o e)
  (at level 65, right associativity) : tlc_core_scope.
Definition WhenSelf {C} : term C _ :=
  (Fd = [] /\ Fo = ^Request) \/
  (Fd = [] /\ Fo = ^Periodic) \/
  exists: i, Fd = [^i] /\ Fo = ^Indication.
Notation "'self'" := (WhenSelf)
  (at level 65, right associativity) : tlc_core_scope.
