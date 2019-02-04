Require Import mathcomp.ssreflect.eqtype.
Require Import mathcomp.ssreflect.ssrbool.
Require Import mathcomp.ssreflect.ssreflect.
Require Import tlc.utility.string.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope string_scope.

(* Type of free variables *)
Inductive variable := V : string -> variable.

(* Equality *)
Section eq.

  (* Boolean equality *)
  Definition variable_eq vl vr :=
    match vl, vr with V sl, V sr => sl == sr end.

  (* Boolean equality reflection *)
  Lemma variable_eqP : Equality.axiom variable_eq.
  Proof.
    case=> [sl] [sr] //=; case H: (sl == sr); move/eqP: H => H //=; subst;
      last by constructor; move=> [].
    by constructor.
  Qed.

  (* EqType canonical structures *)
  Canonical Structure variable_eqMixin := EqMixin variable_eqP.
  Canonical Structure variable_eqType :=
    Eval hnf in EqType variable variable_eqMixin.

End eq.

(* Constructor coercions *)
Coercion V : string >-> variable.
