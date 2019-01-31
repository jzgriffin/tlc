Require Import mathcomp.ssreflect.eqtype.
Require Import mathcomp.ssreflect.ssrbool.
Require Import mathcomp.ssreflect.ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Constructor type *)
Inductive constructor : Type :=
(* Unit *)
| CUnit : constructor
(* Pair *)
| CPair : constructor
(* Boolean *)
| CTrue : constructor
| CFalse : constructor
(* Natural *)
| CZero : constructor
| CSucc : constructor
(* List *)
| CNil : constructor
| CCons : constructor.

(* Equality *)
Section eq.

  (* Boolean equality *)
  Definition constructor_eq cl cr :=
    match cl, cr with
    | CUnit, CUnit => true
    | CUnit, _ => false
    | CPair, CPair => true
    | CPair, _ => false
    | CTrue, CTrue => true
    | CTrue, _ => false
    | CFalse, CFalse => true
    | CFalse, _ => false
    | CZero, CZero => true
    | CZero, _ => false
    | CSucc, CSucc => true
    | CSucc, _ => false
    | CNil, CNil => true
    | CNil, _ => false
    | CCons, CCons => true
    | CCons, _ => false
    end.

  (* Boolean equality reflection *)
  Lemma constructor_eqP : Equality.axiom constructor_eq.
  Proof.
    case; case; by constructor.
  Qed.

  (* EqType canonical structures *)
  Canonical Structure constructor_eqMixin := EqMixin constructor_eqP.
  Canonical Structure constructor_eqType :=
    Eval hnf in EqType constructor constructor_eqMixin.

End eq.
