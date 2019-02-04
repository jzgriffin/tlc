Require Import mathcomp.ssreflect.eqtype.
Require Import mathcomp.ssreflect.ssrbool.
Require Import mathcomp.ssreflect.ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Constructors for value terms *)
Inductive constructor :=
(* Unit *)
| CUnit
(* Product *)
| CPair
(* Sum *)
| CLeft
| CRight
(* Boolean *)
| CTrue
| CFalse
(* Natural *)
| CZero
| CSucc
(* List *)
| CNil
| CCons.

(* Equality *)
Section eq.

  (* Boolean equality *)
  Definition constructor_eq cl cr :=
    match cl, cr with
    (* Unit *)
    | CUnit, CUnit => true
    | CUnit, _ => false
    (* Product *)
    | CPair, CPair => true
    | CPair, _ => false
    (* Sum *)
    | CLeft, CLeft => true
    | CLeft, _ => false
    | CRight, CRight => true
    | CRight, _ => false
    (* Boolean *)
    | CTrue, CTrue => true
    | CTrue, _ => false
    | CFalse, CFalse => true
    | CFalse, _ => false
    (* Natural *)
    | CZero, CZero => true
    | CZero, _ => false
    | CSucc, CSucc => true
    | CSucc, _ => false
    (* List *)
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
