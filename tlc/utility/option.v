(* TLC in Coq
 *
 * Module: tlc.utility.option
 * Purpose: Monad hierarchy typeclass instances for option.
 *)

Require Import mathcomp.ssreflect.ssreflect.
Require Import mathcomp.ssreflect.ssrfun.
Require Import tlc.utility.applicative.
Require Import tlc.utility.functor.
Require Import tlc.utility.monad.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Functor instance for option *)
Instance option_functor : Functor option := {
  map _ _ f x := if x is Some x' then Some (f x') else None;
}.
Proof.
  - by move=> a; case=> //=.
  - by move=> a b c f g; case=> //=.
Defined.

(* Applicative instance for option *)
Instance option_applicative : Applicative option := {
  pure := fun a x => Some x;
  apply _ _ f x :=
    match f, x with
    | Some f', Some x' => Some (f' x')
    | _, _ => None
    end;
}.
Proof.
  - by move=> a; rewrite /left_id; case=> //=.
  - by [].
  - by [].
  - by move=> a b c; case=> [u | ] [v | ] [w | ] //=.
Defined.

(* Monad instance for option *)
Instance option_monad : Monad option _ := {
  bind _ _ x f := if x is Some x' then f x' else None;
}.
Proof.
  - by [].
  - by move=> a; case=> [x | ] //=.
  - by move=> a b c f g; case=> [x | ] //=.
Defined.
