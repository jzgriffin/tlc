Require Import mathcomp.ssreflect.eqtype.
Require Import mathcomp.ssreflect.seq.
Require Import mathcomp.ssreflect.ssrbool.
Require Import mathcomp.ssreflect.ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Implement partial maps as association lists *)
Definition partial_map (key : eqType) value := seq (key * value).

(* Look up the value associated with the given key in a partial map *)
Fixpoint pm_lookup key value (pm : partial_map key value) k :=
  match pm with
  | [::] => None
  | (k', v') :: pm' => if k == k' then Some v' else pm_lookup pm' k
  end.

(* Clear the value associated with the given key in a partial map *)
Definition pm_clear key value (pm : partial_map key value) k :=
  [seq kv <- pm | fst kv != k].

(* Extend a partial map with a new value for the given key *)
Definition pm_extend key value (pm : partial_map key value) k v :=
  (k, v) :: pm_clear pm k.

(* Takes the left-biased union of two partial maps *)
Fixpoint pm_union key value (pml pmr : partial_map key value) :=
  match pml with
  | [::] => pmr
  | (k, v) :: pml' => pm_union pml' (pm_extend pmr k v)
  end.

(* Operator notations *)
Notation "pm {@ k }" := (pm_lookup pm k) (at level 1, left associativity).
Notation "pm {- k }" := (pm_clear pm k) (at level 1, left associativity).
Notation "pm {= k := v }" := (pm_extend pm k v)
  (at level 1, left associativity).
