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

(* Result type for computations that may fail *)
Inductive result error value : Type :=
| Error : error -> result error value
| Value : value -> result error value.

Arguments Error {error value}.
Arguments Value {error value}.

(* Equality *)
Section eq.

  Variable error : eqType.
  Variable value : eqType.

  (* Boolean equality *)
  Definition result_eq (rl rr : result error value) :=
    match rl, rr with
    | Error el, Error er => el == er
    | Error _, _ => false
    | Value vl, Value vr => vl == vr
    | Value _, _ => false
    end.

  (* Boolean equality reflection *)
  Lemma result_eqP : Equality.axiom result_eq.
  Proof.
    case=> [el | vl] [er | vr] /=; (try by constructor);
      try by apply/(iffP idP); [by move/eqP <- | by move=> [] => H; apply/eqP].
  Qed.

  (* EqType canonical structures *)
  Canonical Structure result_eqMixin := EqMixin result_eqP.
  Canonical Structure result_eqType :=
    Eval hnf in EqType (result error value) result_eqMixin.

End eq.

(* Functor instance for result *)
Instance result_functor error : Functor (result error) := {
  map _ _ f r :=
    match r with
    | Error e => Error e
    | Value v => Value (f v)
    end;
}.
Proof.
  - by move=> a; case=> //=.
  - by move=> a b c f g; case=> //=.
Defined.

(* Applicative instance for result *)
Instance result_applicative error : Applicative (result error) := {
  pure := fun _ v => Value v;
  apply _ _ f x :=
    match f with
    | Error e => Error e
    | Value v => v <$> x
    end;
}.
Proof.
  - by move=> a; rewrite /left_id; case=> //=.
  - by [].
  - by [].
  - by move=> a b c; case=> [u | su] [v | sv] [w | sw] //=.
Defined.

(* Monad instance for result *)
Instance result_monad error : Monad (result error) _ := {
  bind _ _ x f :=
    match x with
    | Error e => Error e
    | Value v => f v
    end;
}.
Proof.
  - by [].
  - move=> a; case=> [x | ] //=.
  - move=> a b c f g; case=> [x | ] //=.
Defined.

(* Flattens a list of results into a result of list *)
Fixpoint flatten_results error value (rs : seq (result error value)) :=
  match rs with
  | [::] => pure [::]
  | Value v :: rs => rs <- flatten_results rs; pure (v :: rs)
  | Error e :: _ => Error e
  end.
