Require Import TLC.Term.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* This implementation of restrict is slightly modified from that in the paper,
   which only operates on assertions of a particular form (excluding assertions
   containing next and self assertions).  For now, this implementation simply
   produces a False assertion when an assertion of this form is encountered. *)
Fixpoint restrict {C} (A' : term C Prop) T (A : term C T) : term C T.
Proof.
  destruct A eqn:eqnA.
  - exact A.
  - exact A.
  - apply (Application (restrict _ A' _ t1) (restrict _ A' _ t2)).
  - apply (Not (restrict _ A' _ t)).
  - apply (And (restrict _ A' _ t1) (restrict _ A' _ t2)).
  - apply (Or (restrict _ A' _ t1) (restrict _ A' _ t2)).
  - apply (If (restrict _ A' _ t1) (restrict _ A' _ t2)).
  - apply (ForAll (fun x => restrict _ A' _ (A0 x))).
  - apply (Exists (fun x => restrict _ A' _ (A0 x))).
  - apply (Always' (If A' (restrict _ A' _ t))).
  - apply (AlwaysPast' (If A' (restrict _ A' _ t))).
  - apply (Eventually' (restrict _ A' _ t)).
  - apply (EventuallyPast' (restrict _ A' _ t)).
  - apply (^False)%tlc. (* Deviation *)
  - apply (^False)%tlc. (* Deviation *)
  - apply (Equals (restrict _ A' _ t1) (restrict _ A' _ t2)).
  - exact A.
  - exact A.
  - exact A.
Qed.
