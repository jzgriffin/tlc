(* TLC in Coq
 *
 * Module: tlc.utility.result
 * Purpose: Contains the result monad.
 *)

Require Import mathcomp.ssreflect.eqtype.
Require Import mathcomp.ssreflect.seq.
Require Import mathcomp.ssreflect.ssrbool.
Require Import mathcomp.ssreflect.ssreflect.
Require Import mathcomp.ssreflect.ssrfun.
Require Import tlc.utility.applicative.
Require Import tlc.utility.functor.
Require Import tlc.utility.monad.
Require Import tlc.utility.string.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Result type for computations that may fail
 * Similar to option, but with a parameter for explaining the failure case.
 *)
Inductive result {error value} :=
| Failure (e : error)
| Success (x : value).

Arguments result : clear implicits.

(* Equality *)
Section result_eq.

  Variable error : eqType.
  Variable value : eqType.

  (* Boolean equality *)
  Definition result_eq (rl rr : result error value) :=
    match rl, rr with
    | Failure el, Failure er => el == er
    | Failure _, _ => false
    | Success xl, Success xr => xl == xr
    | Success _, _ => false
    end.

  (* Boolean equality reflection *)
  Lemma result_eqP : Equality.axiom result_eq.
  Proof.
    case=> [el | xl] [er | xr] /=; (try by constructor);
      try by apply/(iffP idP); [by move/eqP <- | by move=> [] => H; apply/eqP].
  Qed.

  (* EqType canonical structures *)
  Canonical Structure result_eqMixin := EqMixin result_eqP.
  Canonical Structure result_eqType :=
    Eval hnf in EqType (result error value) result_eqMixin.

End result_eq.

(* Functor instance for result *)
Instance result_functor error : Functor (result error) := {
  map _ _ f r :=
    match r with
    | Failure e => Failure e
    | Success x => Success (f x)
    end;
}.
Proof.
  - by move=> a; case=> //=.
  - by move=> a b c f g; case=> //=.
Defined.

(* Applicative instance for result *)
Instance result_applicative error : Applicative (result error) := {
  pure := fun _ x => Success x;
  apply _ _ f x :=
    match f with
    | Failure e => Failure e
    | Success f => f <$> x
    end;
}.
Proof.
  - by move=> a; rewrite /left_id; case=> //=.
  - by [].
  - by [].
  - by move=> a b c; case=> [eu | fu] [ev | fv] [ew | fw] //=.
Defined.

(* Monad instance for result *)
Instance result_monad error : Monad (result error) _ := {
  bind _ _ x f :=
    match x with
    | Failure e => Failure e
    | Success x => f x
    end;
}.
Proof.
  - by [].
  - by move=> a; case=> [x | ] //=.
  - by move=> a b c f g; case=> [x | ] //=.
Defined.

(* Flattens a list of results into a result of list
 * If any element of the list is a failure, the result is a failure.
 *)
Fixpoint flatten_results error value (rs : seq (result error value)) :=
  match rs with
  | [::] => pure [::]
  | Failure e :: _ => Failure e
  | Success x :: rs => rs <- flatten_results rs; pure (x :: rs)
  end.
