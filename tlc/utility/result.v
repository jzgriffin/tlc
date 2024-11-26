(* TLC in Coq
 *
 * Module: tlc.utility.result
 * Purpose: Contains the result monad.
 *)

From HB Require Import structures.
Require Import mathcomp.ssreflect.eqtype.
Require Import mathcomp.ssreflect.seq.
Require Import mathcomp.ssreflect.ssrbool.
Require Import mathcomp.ssreflect.ssreflect.
Require Import mathcomp.ssreflect.ssrfun.
Require Import tlc.utility.monad.

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
Section eq.

  Variable error : eqType.
  Variable value : eqType.

  (* Boolean equality *)
  Definition result_eq (r1 r2 : result error value) :=
    match r1, r2 with
    | Failure e1, Failure e2 => e1 == e2
    | Success x1, Success x2 => x1 == x2
    | _, _ => false
    end.

  (* Boolean equality reflection *)
  Lemma result_eqP : Equality.axiom result_eq.
  Proof.
    move; case=> [e1 | x1] [e2 | x2] //=; try by constructor.
    - by have [<- | neqx] := e1 =P e2; last (by right; case); constructor.
    - by have [<- | neqx] := x1 =P x2; last (by right; case); constructor.
  Qed.

  (* EqType canonical structures *)
  HB.instance Definition _ := hasDecEq.Build (result error value) result_eqP.

End eq.

(* Functor instance for result *)
#[refine]
Instance result_functor error : Functor (result error) := {
  map _ _ f r :=
    match r with
    | Failure e => Failure e
    | Success x => Success (f x)
    end;
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

(* Applicative instance for result *)
#[refine]
Instance result_applicative error : Applicative (result error) := {
  pure := fun _ x => Success x;
  apply _ _ f x :=
    match f with
    | Failure e => Failure e
    | Success f => f <$> x
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
    by move=> ???; case=> [? | ?] [? | ?] [? | ?].
  }
Defined.

(* Monad instance for result *)
#[refine]
Instance result_monad error : Monad (result error) := {
  bind _ _ x f :=
    match x with
    | Failure e => Failure e
    | Success x => f x
    end;
}.
Proof.
  (* bind_left_id *)
  {
    by [].
  }

  (* bind_right_id *)
  {
    by move=> ?; case=> [? | ?].
  }

  (* bind_assoc *)
  {
    by move=> ?????; case=> [? | ?].
  }
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
