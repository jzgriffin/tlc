(* TLC in Coq
 *
 * Module: tlc.syntax.parameter
 * Purpose: Contains the syntax of parameters.
 *)

Require Import mathcomp.ssreflect.eqtype.
Require Import mathcomp.ssreflect.ssrbool.
Require Import mathcomp.ssreflect.ssreflect.
Require Import mathcomp.ssreflect.ssrnat.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Type of bound variables
 * i is the distance to the containing binder
 * j is the index of the binding within its binder
 * This type comes from the locally nameless representation.
 *)
Inductive parameter := P (i j : nat).

(* Equality *)
Section eq.

  (* Boolean equality *)
  Definition parameter_eq pl pr :=
    match pl, pr with P il jl, P ir jr => (il == ir) && (jl == jr) end.

  (* Boolean equality reflection *)
  Lemma parameter_eqP : Equality.axiom parameter_eq.
  Proof.
    case=> [il jl] [ir jr] //=.
    case H: (il == ir); move/eqP: H => H //=; subst;
      last by constructor; move=> [].
    case H: (jl == jr); move/eqP: H => H //=; subst;
      last by constructor; move=> [].
    by constructor.
  Qed.

  (* EqType canonical structures *)
  Canonical Structure parameter_eqMixin :=
    Eval hnf in EqMixin parameter_eqP.
  Canonical Structure parameter_eqType :=
    Eval hnf in EqType parameter parameter_eqMixin.

End eq.
