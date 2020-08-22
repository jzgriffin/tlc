(* TLC in Coq
 *
 * Module: tlc.syntax.function
 * Purpose: Contains the syntax of functions.
 *)

Require Import mathcomp.ssreflect.choice.
Require Import mathcomp.ssreflect.eqtype.
Require Import mathcomp.ssreflect.ssrbool.
Require Import mathcomp.ssreflect.ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Externally implemented function terms
 * These are functions that cannot be expressed directly within the term
 * language.  Functions that must be defined recursively are among this class.
 *)
Inductive function :=
(* Boolean equality *)
| FEqual
(* Naturals *)
| FAdd
(* Lists *)
| FMap
| FCount
| FConcat
| FSetUnion.

(* Equality *)
Section eq.

  (* Boolean equality *)
  Definition function_eq f1 f2 :=
    match f1, f2 with
    (* Boolean equality *)
    | FEqual, FEqual => true
    (* Naturals *)
    | FAdd, FAdd => true
    (* Lists *)
    | FMap, FMap => true
    | FCount, FCount => true
    | FConcat, FConcat => true
    | FSetUnion, FSetUnion => true
    (* Unequal *)
    | _, _ => false
    end.

  (* Boolean equality reflection *)
  Lemma function_eqP : Equality.axiom function_eq.
  Proof.
    by case; case; constructor.
  Qed.

  (* EqType canonical structures *)
  Definition function_eqMixin := EqMixin function_eqP.
  Canonical function_eqType := EqType function function_eqMixin.

End eq.
