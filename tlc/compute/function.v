Require Import mathcomp.ssreflect.eqtype.
Require Import mathcomp.ssreflect.ssrbool.
Require Import mathcomp.ssreflect.ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Function type *)
Inductive function : Type :=
(* Any *)
| FEqual : function
(* Natural *)
| FAdd : function
(* List *)
| FMember : function
| FCount : function
| FUnion : function
| FMap : function.

(* Equality *)
Section eq.

  (* Boolean equality *)
  Definition function_eq fl fr :=
    match fl, fr with
    | FEqual, FEqual => true
    | FEqual, _ => false
    | FAdd, FAdd => true
    | FAdd, _ => false
    | FMember, FMember => true
    | FMember, _ => false
    | FCount, FCount => true
    | FCount, _ => false
    | FUnion, FUnion => true
    | FUnion, _ => false
    | FMap, FMap => true
    | FMap, _ => false
    end.

  (* Boolean equality reflection *)
  Lemma function_eqP : Equality.axiom function_eq.
  Proof.
    case; case; by constructor.
  Qed.

  (* EqType canonical structures *)
  Canonical Structure function_eqMixin := EqMixin function_eqP.
  Canonical Structure function_eqType :=
    Eval hnf in EqType function function_eqMixin.

End eq.
