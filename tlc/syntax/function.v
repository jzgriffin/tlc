(* TLC in Coq
 *
 * Module: tlc.syntax.function
 * Purpose: Contains the syntax of functions.
 *)

Require Import mathcomp.ssreflect.eqtype.
Require Import mathcomp.ssreflect.ssrbool.
Require Import mathcomp.ssreflect.ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Externally implemented function terms
 * These are functions that either cannot be encoded directly within the term
 * language or are inconvenient to do so.  For example, equality obviously
 * cannot be represented within this limited term language.  Functions that
 * must be implemented recursively also cannot be easily represented.
 *)
Inductive function :=
(* Generic *)
| FEqual (* equal x y *)
(* Boolean *)
| FNot (* not x *)
| FOr (* or x y *)
(* Natural *)
| FSucc (* succ x *)
| FAdd (* add x y *)
(* List *)
| FConcat (* concat xs ys *)
| FCount (* count x xs *)
| FUnion (* union xs ys *)
| FMap (* map f xs *).

(* Equality *)
Section eq.

  (* Boolean equality *)
  Definition function_eq fl fr :=
    match fl, fr with
    (* Generic *)
    | FEqual, FEqual => true
    | FEqual, _ => false
    (* Boolean *)
    | FNot, FNot => true
    | FNot, _ => false
    | FOr, FOr => true
    | FOr, _ => false
    (* Natural *)
    | FSucc, FSucc => true
    | FSucc, _ => false
    | FAdd, FAdd => true
    | FAdd, _ => false
    (* List *)
    | FConcat, FConcat => true
    | FConcat, _ => false
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
  Canonical Structure function_eqMixin :=
    Eval hnf in EqMixin function_eqP.
  Canonical Structure function_eqType :=
    Eval hnf in EqType function function_eqMixin.

End eq.
