Require Import mathcomp.ssreflect.eqtype.
Require Import mathcomp.ssreflect.seq.
Require Import mathcomp.ssreflect.ssrbool.
Require Import mathcomp.ssreflect.ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Implement sets as sequences *)
Definition set (T : eqType) := seq T.

(* Big union of set of sets *)
Definition big_union T (tss : seq (set T)) := undup (flatten tss).

(* Union of two sets *)
Definition union T (ts1 ts2 : set T) := undup (ts1 ++ ts2).

(* Set 1 without the elements of set 2 *)
Definition difference T (ts1 ts2 : set T) := [seq t <- ts1 | t \notin ts2].

(* Operator notations *)
Notation "ts1 \union ts2" := (union ts1 ts2)
  (at level 30, right associativity).
Notation "ts1 \diff ts2" := (difference ts1 ts2)
  (at level 30, right associativity).
