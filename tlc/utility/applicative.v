Require Import mathcomp.ssreflect.ssreflect.
Require Import mathcomp.ssreflect.ssrfun.
Require Import tlc.utility.functor.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Export tlc.utility.functor.

(* Applicative functor type class *)
Class Applicative f `{Functor f} := {
  pure : forall a, a -> f a;
  apply : forall a b, f (a -> b) -> f a -> f b;
  apply_left_id : forall a, left_id (pure (@id a)) (@apply a a);
  apply_homo : forall a b (f : a -> b) x,
    apply (pure f) (pure x) = pure (f x);
  apply_inter : forall a b (u : f (a -> b)) y,
    apply u (pure y) = apply (pure (fun g => g y)) u;
  apply_comp : forall a b c (u : f (b -> c)) (v : f (a -> b)) (w : f a),
    apply (apply (apply (pure comp) u) v) w = apply u (apply v w);
}.

Arguments Applicative f {_}.

(* Applicative functor notations *)
Notation "x <*> y" := (apply x y) (at level 50, left associativity).
