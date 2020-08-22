(* TLC in Coq
 *
 * Module: tlc.semantics.assertion
 * Purpose: Contains the semantics for assertion forms.
 *)

Require Import mathcomp.ssreflect.eqtype.
Require Import mathcomp.ssreflect.seq.
Require Import mathcomp.ssreflect.ssrbool.
Require Import mathcomp.ssreflect.ssreflect.
Require Import mathcomp.ssreflect.ssrnat.
Require Import tlc.semantics.error.
Require Import tlc.semantics.predicate.
Require Import tlc.semantics.term.
Require Import tlc.syntax.all_syntax.
Require Import tlc.utility.monad.
Require Import tlc.utility.result.
Require Import tlc.utility.seq.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Determine whether an asserion is a universal quantification *)
Definition assertion_univ A := if A is AForAll _ then true else false.

(* Open an assertion A at depth k with bindings us *)
Fixpoint open_assertion_at k us A :=
  match A with
  | AFalse => pure A
  | APredicate p => APredicate <$> open_predicate_at k us p
  | ANot A => ANot <$> open_assertion_at k us A
  | AAnd A1 A2 =>
    A1 <- open_assertion_at k us A1;
    A2 <- open_assertion_at k us A2;
    pure (AAnd A1 A2)
  | AForAll A => AForAll <$> open_assertion_at k.+1 us A
  | AApplication A t =>
    A <- open_assertion_at k us A;
    t <- open_term_at k us t;
    pure (AApplication A t)
  | AAlways' A => AAlways' <$> open_assertion_at k us A
  | AAlwaysP' A => AAlwaysP' <$> open_assertion_at k us A
  | AEventually' A => AEventually' <$> open_assertion_at k us A
  | AEventuallyP' A => AEventuallyP' <$> open_assertion_at k us A
  | ANext A => ANext <$> open_assertion_at k us A
  | APrevious A => APrevious <$> open_assertion_at k us A
  | ASelf A => ASelf <$> open_assertion_at k us A
  end.
Definition open_assertion := open_assertion_at 0.

(* Determine whether an assertion is locally closed
 * An assertion is locally closed if every parameter reference is well-formed.
 *)
Fixpoint assertion_lc_in ks A :=
  match A with
  | AFalse => true
  | APredicate p => predicate_lc_in ks p
  | ANot A => assertion_lc_in ks A
  | AAnd A1 A2 => assertion_lc_in ks A1 && assertion_lc_in ks A2
  | AForAll A => assertion_lc_in (1 :: ks) A
  | AApplication A t => assertion_lc_in ks A && term_lc_in ks t
  | AAlways' A => assertion_lc_in ks A
  | AAlwaysP' A => assertion_lc_in ks A
  | AEventually' A => assertion_lc_in ks A
  | AEventuallyP' A => assertion_lc_in ks A
  | ANext A => assertion_lc_in ks A
  | APrevious A => assertion_lc_in ks A
  | ASelf A => assertion_lc_in ks A
  end.
Definition assertion_lc := assertion_lc_in [::].

(* Any assertion that is closed at depth ks is closed at depth k :: ks *)
Lemma assertion_lc_in_cons k ks A :
  assertion_lc_in ks A ->
  assertion_lc_in (k :: ks) A.
Proof.
Admitted.

(* Any assertion that is closed at depth ks is closed at depth ks' ++ ks *)
Lemma assertion_lc_in_concat ks' ks A :
  assertion_lc_in ks A ->
  assertion_lc_in (ks' ++ ks) A.
Proof.
  elim: ks' => [| k ks' IH] //=.
  by move=> H; specialize (IH H); apply assertion_lc_in_cons.
Qed.

(* Opening a closed assertion at a depth above its closure depth has no effect *)
Lemma open_lc_assertion_at k ks us A :
  k >= size ks ->
  assertion_lc_in ks A ->
  open_assertion_at k us A = Success A.
Proof.
Admitted.

(* Compute the set of flexible variables appearing in an assertion *)
Fixpoint assertion_flexibles A :=
  match A with
  | AFalse => [::]
  | APredicate p => predicate_flexibles p
  | ANot A => assertion_flexibles A
  | AAnd A1 A2 => assertion_flexibles A1 ++ assertion_flexibles A2
  | AForAll A => assertion_flexibles A
  | AApplication A t => assertion_flexibles A ++ term_flexibles t
  | AAlways' A => assertion_flexibles A
  | AAlwaysP' A => assertion_flexibles A
  | AEventually' A => assertion_flexibles A
  | AEventuallyP' A => assertion_flexibles A
  | ANext A => assertion_flexibles A
  | APrevious A => assertion_flexibles A
  | ASelf A => assertion_flexibles A
  end.

(* Compute the set of rigid variables appearing in an assertion *)
Fixpoint assertion_rigids A :=
  match A with
  | AFalse => [::]
  | APredicate p => predicate_rigids p
  | ANot A => assertion_rigids A
  | AAnd A1 A2 => assertion_rigids A1 ++ assertion_rigids A2
  | AForAll A => assertion_rigids A
  | AApplication A t => assertion_rigids A ++ term_rigids t
  | AAlways' A => assertion_rigids A
  | AAlwaysP' A => assertion_rigids A
  | AEventually' A => assertion_rigids A
  | AEventuallyP' A => assertion_rigids A
  | ANext A => assertion_rigids A
  | APrevious A => assertion_rigids A
  | ASelf A => assertion_rigids A
  end.

(* Compute the set of variables appearing in an assertion *)
Definition assertion_vars A :=
  map VF (assertion_flexibles A) ++ map VR (assertion_rigids A).

(* Determine whether an assertion is globally closed
 * An assertion is globally closed if it contains no rigid variables.
 *)
Definition assertion_gc_in xs A := subset (assertion_rigids A) xs.
Definition assertion_gc := assertion_gc_in [::].

(* Determine whether an assertion is closed
 * An assertion is closed if it is locally and globally closed.
 *)
Definition assertion_closed_in ks xs A :=
  assertion_lc_in ks A && assertion_gc_in xs A.
Definition assertion_closed A := assertion_lc A && assertion_gc A.

(* A closed assertion is locally closed *)
Lemma closed_assertion_lc ks xs A :
  assertion_closed_in ks xs A ->
  assertion_lc_in ks A.
Proof.
  by move/andP => [??].
Qed.

(* A closed assertion is globally closed *)
Lemma closed_assertion_gc ks xs A :
  assertion_closed_in ks xs A ->
  assertion_gc_in xs A.
Proof.
  by move/andP => [??].
Qed.

(* Determine whether an assertion is rigid
 * An assertion is rigid if it contains no flexible variables.
 *)
Fixpoint assertion_rigid A :=
  match A with
  | AFalse => true
  | APredicate p => predicate_rigid p
  | ANot A => assertion_rigid A
  | AAnd A1 A2 => assertion_rigid A1 && assertion_rigid A2
  | AForAll A => assertion_rigid A
  | AApplication A t => assertion_rigid A && term_rigid t
  | AAlways' A => assertion_rigid A
  | AAlwaysP' A => assertion_rigid A
  | AEventually' A => assertion_rigid A
  | AEventuallyP' A => assertion_rigid A
  | ANext A => assertion_rigid A
  | APrevious A => assertion_rigid A
  | ASelf A => assertion_rigid A
  end.

(* Replace all instances of variable x with term u within A *)
Fixpoint replace_assertion_var x u A :=
  match A with
  | AFalse => A
  | APredicate p => APredicate (replace_predicate_var x u p)
  | ANot A => ANot (replace_assertion_var x u A)
  | AAnd A1 A2 =>
    AAnd (replace_assertion_var x u A1) (replace_assertion_var x u A2)
  | AForAll A => AForAll (replace_assertion_var x u A)
  | AApplication A t =>
    AApplication (replace_assertion_var x u A) (replace_term_var x u t)
  | AAlways' A => AAlways' (replace_assertion_var x u A)
  | AAlwaysP' A => AAlwaysP' (replace_assertion_var x u A)
  | AEventually' A => AEventually' (replace_assertion_var x u A)
  | AEventuallyP' A => AEventuallyP' (replace_assertion_var x u A)
  | ANext A => ANext (replace_assertion_var x u A)
  | APrevious A => APrevious (replace_assertion_var x u A)
  | ASelf A => ASelf (replace_assertion_var x u A)
  end.

(* Determine whether all occurrences of A' within A are positive or negative
 * p' is the positivity to check for; true for positive, false for negative.
 * p is the current positivity.
 *)
Fixpoint all_assertion_occ_rec A' p' A p :=
  if A == A' then p == p' else
  match A with
  | AFalse => true
  | APredicate _ => true
  | ANot A => all_assertion_occ_rec A' p' A (~~p)
  | AAnd A1 A2 =>
    all_assertion_occ_rec A' p' A1 p && all_assertion_occ_rec A' p' A2 p
  | AForAll A => all_assertion_occ_rec A' p' A p
  | AApplication A _ => all_assertion_occ_rec A' p' A p
  | AAlways' A => all_assertion_occ_rec A' p' A p
  | AAlwaysP' A => all_assertion_occ_rec A' p' A p
  | AEventually' A => all_assertion_occ_rec A' p' A p
  | AEventuallyP' A => all_assertion_occ_rec A' p' A p
  | ANext A => all_assertion_occ_rec A' p' A p
  | APrevious A => all_assertion_occ_rec A' p' A p
  | ASelf A => all_assertion_occ_rec A' p' A p
  end.
Definition all_assertion_occ_pos A' A := all_assertion_occ_rec A' true A true.
Definition all_assertion_occ_neg A' A := all_assertion_occ_rec A' false A true.

(* Replace all instances of assertion x with assertion u in A *)
Fixpoint replace_assertion x u A :=
  if A == x then u else
  match A with
  | AFalse => A
  | APredicate _ => A
  | ANot A => ANot (replace_assertion x u A)
  | AAnd A1 A2 => AAnd (replace_assertion x u A1) (replace_assertion x u A2)
  | AForAll A => AForAll (replace_assertion x u A)
  | AApplication A t => AApplication (replace_assertion x u A) t
  | AAlways' A => AAlways' (replace_assertion x u A)
  | AAlwaysP' A => AAlwaysP' (replace_assertion x u A)
  | AEventually' A => AEventually' (replace_assertion x u A)
  | AEventuallyP' A => AEventuallyP' (replace_assertion x u A)
  | ANext A => ANext (replace_assertion x u A)
  | APrevious A => APrevious (replace_assertion x u A)
  | ASelf A => ASelf (replace_assertion x u A)
  end.

(* Reduce the subterms of assertion A *)
Reserved Notation "[[A A ]]" (at level 0, no associativity).
Fixpoint reduce_assertion A :=
  match A with
  | AFalse => pure A
  | APredicate p => APredicate <$> [[P p]]
  | ANot A => ANot <$> [[A A]]
  | AAnd A1 A2 =>
    A1 <- [[A A1]];
    A2 <- [[A A2]];
    pure (AAnd A1 A2)
  | AForAll A => AForAll <$> [[A A]]
  | AApplication A t =>
    A <- [[A A]];
    t <- [[t t]];
    if A is AForAll A then
      let us := [:: t] in
      match open_assertion us A with
      | Success A => Success A
      | Failure (k, x) => Failure (EOpenAssertion A us k x)
      end
    else pure (AApplication A t)
  | AAlways' A => AAlways' <$> [[A A]]
  | AAlwaysP' A => AAlwaysP' <$> [[A A]]
  | AEventually' A => AEventually' <$> [[A A]]
  | AEventuallyP' A => AEventuallyP' <$> [[A A]]
  | ANext A => ANext <$> [[A A]]
  | APrevious A => APrevious <$> [[A A]]
  | ASelf A => ASelf <$> [[A A]]
  end
  where "[[A A ]]" := (reduce_assertion A).
