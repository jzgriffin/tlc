Require Import mathcomp.ssreflect.eqtype.
Require Import mathcomp.ssreflect.seq.
Require Import mathcomp.ssreflect.ssrbool.
Require Import mathcomp.ssreflect.ssreflect.
Require Import tlc.utility.string.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope string_scope.

(* Variable type *)
Inductive variable : Type :=
| V : string -> variable.

(* Constructor coercions *)
Coercion V : string >-> variable.

(* Equality *)
Section eq.

  (* Boolean equality *)
  Definition variable_eq vl vr :=
    match vl, vr with V sl, V sr => sl == sr end.

  (* Boolean equality reflection *)
  Lemma variable_eqP : Equality.axiom variable_eq.
  Proof.
    case=> [sl] [sr]; case Hs: (sl == sr); rewrite /= Hs; constructor;
      move/eqP: Hs => Hs; first by rewrite Hs.
    by move=> [].
  Qed.

  (* EqType canonical structures *)
  Canonical Structure variable_eqMixin := EqMixin variable_eqP.
  Canonical Structure variable_eqType :=
    Eval hnf in EqType variable variable_eqMixin.

End eq.

(* Fresh variable generation *)
Definition next_variable v :=
  match v with V s => V (s ++ "'") end.

Fixpoint fresh_variable v vs :=
  match vs with
  | nil => v
  | v' :: vs' => fresh_variable (if v == v' then next_variable v else v) vs'
  end.
