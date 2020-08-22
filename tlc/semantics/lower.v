(* TLC in Coq
 *
 * Module: tlc.semantics.lower
 * Purpose: Contains the assertion lowering transformation.
 *)

Require Import mathcomp.ssreflect.seq.
Require Import mathcomp.ssreflect.ssreflect.
Require Import tlc.syntax.all_syntax.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Push an assertion from the top to a lower layer i *)
Definition push_assertion (i : nat) A (TA : top_assertion A) :=
  location_assertion_rec
    (fun _ n dp o e => {-A on n,
      (Fd = term_of_list (map term_of_nat (rcons dp i)) /\ Fo = o /\ Fe = e) -})
    (fun _ n => {-A n \in UCorrect -})
    (fun d A (_ : location_assertion d A) A' => {-A ~A' -})
    (fun d A1 A2 (_ : location_assertion d A1) A1' (_ : location_assertion d A2) A2' =>
      {-A A1' /\ A2' -})
    (fun d A (_ : location_assertion d A) A' => {-A forall: A' -})
    (fun d A t (_ : location_assertion d A) A' => {-A A' ' t -})
    (fun d A (_ : location_assertion d A) A' => {-A always^ A' -})
    (fun d A (_ : location_assertion d A) A' => {-A alwaysp^ A' -})
    (fun d A (_ : location_assertion d A) A' => {-A eventually^ A' -})
    (fun d A (_ : location_assertion d A) A' => {-A eventuallyp^ A' -}) TA.

(* Restrict an assertion to remain valid on traces that are extended with
 * interleaving events
 *
 * NOTE: This algorithm is slightly different from the algorithm in TLC.  The
 * true algorithm operates on a subset of assertions.  This algorithm operates
 * on all assertions, but returns false when an illegal assertion is given.
 *)
Fixpoint restrict_assertion A' A :=
  match A with
  | AFalse => A
  | APredicate _ => A
  | ANot A => {-A ~restrict_assertion A' A -}
  | AAnd Al Ar => {-A restrict_assertion A' Al /\ restrict_assertion A' Ar -}
  | AForAll A => {-A forall: restrict_assertion A' A -}
  | AApplication A t => {-A A ' t -}
  | AAlways' A => {-A always^ (A' -> restrict_assertion A' A) -}
  | AAlwaysP' A => {-A alwaysp^ (A' -> restrict_assertion A' A) -}
  | AEventually' A => {-A eventually^ (restrict_assertion A' A) -}
  | AEventuallyP' A => {-A eventuallyp^ (restrict_assertion A' A) -}
  | ANext _ => AFalse (* Illegal restrict *)
  | APrevious _ => AFalse (* Illegal restrict *)
  | ASelf _ => AFalse (* Illegal restrict *)
  end.

(* Lower a component assertion by first pushing then restricting *)
Definition lower_assertion (i : nat) A (TA : top_assertion A) :=
  restrict_assertion {-A Fd <<< [term_of_nat i] -} (push_assertion i TA).
