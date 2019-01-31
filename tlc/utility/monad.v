Require Import mathcomp.ssreflect.ssreflect.
Require Import mathcomp.ssreflect.ssrfun.
Require Import tlc.utility.applicative.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Export tlc.utility.applicative.

(* Monad type class *)
Class Monad m `{Applicative m} := {
  bind : forall a b, m a -> (a -> m b) -> m b;
  bind_left_id : forall a b (f : (a -> m b)) x, bind (pure x) f = f x;
  bind_right_id : forall a (x : m a), bind x (pure (a := a)) = x;
  bind_assoc : forall a b c (f : (a -> m b)) (g : (b -> m c)) x,
    bind x (fun y => bind (f y) g) = bind (bind x f) g;
}.

Arguments Monad m {_}.

(* Monad notations *)
Notation "x >>= y" := (bind x y) (at level 40, left associativity).
Notation "x <- y ; z" := (y >>= (fun x => z))
  (at level 30, right associativity).
