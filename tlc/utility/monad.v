(* TLC in Coq
 *
 * Module: tlc.utility.monad
 * Purpose: Contains the monad typeclass.
 *)

Require Import mathcomp.ssreflect.ssreflect.
Require Import mathcomp.ssreflect.ssrfun.
Require Import tlc.utility.applicative.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Export tlc.utility.applicative.

(* Monad typeclass
 * A monad consists of an applicative functor, the bind operation, and proofs of
 * the monad laws.
 *)
Class Monad M `{Applicative M} := {
  bind A B : M A -> (A -> M B) -> M B;
  bind_left_id A B (f : A -> M B) x : bind (pure x) f = f x;
  bind_right_id A (x : M A) : bind x (pure (A := A)) = x;
  bind_assoc A B C (f : A -> M B) (g : B -> M C) x :
    bind x (fun y => bind (f y) g) = bind (bind x f) g;
}.

Arguments Monad M {_} {_}.

(* Monad notations *)
Notation "x >>= y" := (bind x y) (at level 40, left associativity).
Notation "x <- y ; z" := (y >>= (fun x => z))
  (at level 30, right associativity). (* Mimics the do-notation of Haskell *)
