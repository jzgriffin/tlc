Require Import mathcomp.ssreflect.eqtype.
Require Import mathcomp.ssreflect.seq.
Require Import mathcomp.ssreflect.ssrbool.
Require Import mathcomp.ssreflect.ssreflect.
Require Import mathcomp.ssreflect.ssrnat.
Require Import tlc.syntax.assertion.
Require Import tlc.utility.seq.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Pushes an assertion from the top to a lower layer i *)
(* TODO: Consider rewriting this in Gallina using the convoy pattern *)
Fixpoint push_assertion (i : nat) A (TA : top_assertion A) : top_assertion_t.
Proof.
  inversion TA; subst.
  - have TA' := LAEventOn tn to te (extension_cons i H).
    by apply (existT _ _ TA').
  - by apply (existT _ _ TA).
  - have E_TA := push_assertion i _ X.
    by apply (existT _ _ (LANot (projT2 E_TA))).
  - have E_TAl := push_assertion i _ X.
    have E_TAr := push_assertion i _ X0.
    by apply (existT _ _ (LAAnd (projT2 E_TAl) (projT2 E_TAr))).
  - have E_TA := push_assertion i _ X.
    by apply (existT _ _ (LAForAll v (projT2 E_TA))).
  - have E_TA := push_assertion i _ X.
    by apply (existT _ _ (LAAlways' (projT2 E_TA))).
  - have E_TA := push_assertion i _ X.
    by apply (existT _ _ (LAAlwaysP' (projT2 E_TA))).
  - have E_TA := push_assertion i _ X.
    by apply (existT _ _ (LAEventually' (projT2 E_TA))).
  - have E_TA := push_assertion i _ X.
    by apply (existT _ _ (LAEventuallyP' (projT2 E_TA))).
Defined.
