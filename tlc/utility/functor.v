(* TLC in Coq
 *
 * Module: tlc.utility.functor
 * Purpose: Contains the functor typeclass.
 *)

Require Import mathcomp.ssreflect.ssreflect.
Require Import mathcomp.ssreflect.ssrfun.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Functor typeclass
 * A functor consists of both the map operation and proofs of the functor laws.
 *)
Class Functor (F : Type -> Type) := {
  map A B : (A -> B) -> F A -> F B;
  map_id A x : map (@id A) x = x;
  map_comp A B C (f : B -> C) (g : A -> B) x :
    map (f \o g) x = (map f \o map g) x;
}.

(* Functor notations *)
Notation "x <$> y" := (map x y) (at level 50, left associativity).
