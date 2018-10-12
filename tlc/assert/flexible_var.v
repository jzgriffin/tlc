From mathcomp.ssreflect
Require Import ssreflect eqtype ssrbool.
From tlc.utility
Require Import indeq.
From tlc.assert
Require Import type.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Named flexible variables in the assertion language *)
Inductive flexible_var : Type :=
| Fn
| Fd
| Fo
| Fe
| Fors
| Fois
| Fs
| Fs'.

(* Equality *)
Section eq.

  Definition flexible_var_eq (x x' : flexible_var) :=
    match x, x' with
    | Fn, Fn => true
    | Fd, Fd => true
    | Fo, Fo => true
    | Fe, Fe => true
    | Fors, Fors => true
    | Fois, Fois => true
    | Fs, Fs => true
    | Fs', Fs' => true
    | _, _ => false
    end.

  Lemma flexible_var_eqP : Equality.axiom flexible_var_eq.
  Proof.
    case; case; by indeq_auto.
  Qed.

  Canonical flexible_var_eqMixin :=
    EqMixin flexible_var_eqP.
  Canonical flexible_var_eqType :=
    Eval hnf in EqType flexible_var flexible_var_eqMixin.

End eq.

(* Maps flexible variables to their types *)
Definition type_flexible_var {C} x : @type C :=
  match x with
  | Fn => Node
  | Fd => Depth
  | Fo => Orientation
  | Fe => Event
  | Fors => [OREvent]
  | Fois => [OIEvent]
  | Fs => States
  | Fs' => States
  end.
