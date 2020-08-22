(* TLC in Coq
 *
 * Module: tlc.utility.applicative
 * Purpose: Contains the applicative functor typeclass.
 *)

Require Import mathcomp.ssreflect.ssreflect.
Require Import mathcomp.ssreflect.ssrfun.
Require Import tlc.utility.functor.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Export tlc.utility.functor.

(* Applicative functor typeclass
 * An applicative functor consists of a functor, the pure and apply operations,
 * and proofs of the applicative functor laws.
 *)
Class Applicative F `{Functor F} := {
  pure A : A -> F A;
  apply A B : F (A -> B) -> F A -> F B;
  apply_left_id A : left_id (pure (@id A)) (@apply A A);
  apply_homo A B (f : A -> B) x :
    apply (pure f) (pure x) = pure (f x);
  apply_inter A B (u : F (A -> B)) y :
    apply u (pure y) = apply (pure (fun f => f y)) u;
  apply_comp A B C (u : F (B -> C)) (v : F (A -> B)) (w : F A) :
    apply (apply (apply (pure comp) u) v) w = apply u (apply v w);
}.

Arguments Applicative F {_}.

(* Applicative functor notations *)
Notation "x <*> y" := (apply x y) (at level 50, left associativity).
