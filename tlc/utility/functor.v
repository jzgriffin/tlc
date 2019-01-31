Require Import mathcomp.ssreflect.ssreflect.
Require Import mathcomp.ssreflect.ssrfun.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Functor type class *)
Class Functor (f : Type -> Type) := {
  map : forall a b, (a -> b) -> f a -> f b;
  map_id : forall a x, map (@id a) x = x;
  map_comp : forall a b c (f : b -> c) (g : a -> b) x,
    map (f \o g) x = (map f \o map g) x;
}.

(* Functor notations *)
Notation "x <$> y" := (map x y) (at level 50, left associativity).
