(* TLC in Coq
 *
 * Module: tlc.utility.option
 * Purpose: Monad hierarchy typeclass instances for option.
 *)

Require Import mathcomp.ssreflect.ssreflect.
Require Import mathcomp.ssreflect.ssrfun.
Require Import tlc.utility.monad.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Functor instance for option *)
#[refine]
Instance option_functor : Functor option := {
  map _ _ f x := if x is Some x' then Some (f x') else None;
}.
Proof.
  (* map_id *)
  {
    by move=> ?; case.
  }

  (* map_comp *)
  {
    by move=> ?????; case.
  }
Defined.

(* Applicative instance for option *)
#[refine]
Instance option_applicative : Applicative option := {
  pure := fun a x => Some x;
  apply _ _ f x :=
    match f, x with
    | Some f', Some x' => Some (f' x')
    | _, _ => None
    end;
}.
Proof.
  (* apply_left_id *)
  {
    by move=> ?; rewrite /left_id; case.
  }

  (* apply_homo *)
  {
    by [].
  }

  (* apply_inter *)
  {
    by [].
  }

  (* apply_comp *)
  {
    by move=> ???; case=> [? |] [? |] [? |].
  }
Defined.

(* Monad instance for option *)
#[refine]
Instance option_monad : Monad option := {
  bind _ _ x f := if x is Some x' then f x' else None;
}.
Proof.
  (* bind_left_id *)
  {
    by [].
  }

  (* bind_right_id *)
  {
    by move=> ?; case=> [? | ].
  }

  (* bind_assoc *)
  {
    by move=> ?????; case=> [? | ].
  }
Defined.
