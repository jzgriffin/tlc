(* TLC in Coq
 *
 * Module: tlc.semantics.assertion
 * Purpose: Contains the semantics for assertion forms.
 *)

Require Import mathcomp.ssreflect.eqtype.
Require Import mathcomp.ssreflect.seq.
Require Import mathcomp.ssreflect.ssrbool.
Require Import mathcomp.ssreflect.ssreflect.
Require Import mathcomp.ssreflect.ssrfun.
Require Import mathcomp.ssreflect.ssrnat.
Require Import tlc.semantics.error.
Require Import tlc.semantics.predicate.
Require Import tlc.semantics.term.
Require Import tlc.syntax.all_syntax.
Require Import tlc.utility.monad.
Require Import tlc.utility.option.
Require Import tlc.utility.partial_map.
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

Fixpoint open_assertion_multi uss A :=
  match uss, A with
  | us :: uss, AForAll A =>
    A <- open_assertion us A;
    open_assertion_multi uss A
  | us :: uss, _ => Failure (0, P 0 0)
  | [::], _ => pure A
  end.

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

(* Well-formed opening will not fail *)
Lemma open_closed_assertion_at ks xs k us A :
  assertion_closed_in ks xs A ->
  onth ks k = Some (size us) ->
  exists A', open_assertion_at k us A = Success A'.
Proof.
Admitted.

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

(* Replace all instances of term x with term u within A *)
Fixpoint replace_assertion_term x u A :=
  match A with
  | AFalse => A
  | APredicate p => APredicate (replace_predicate_term x u p)
  | ANot A => ANot (replace_assertion_term x u A)
  | AAnd A1 A2 =>
    AAnd (replace_assertion_term x u A1) (replace_assertion_term x u A2)
  | AForAll A => AForAll (replace_assertion_term x u A)
  | AApplication A t =>
    AApplication (replace_assertion_term x u A) (replace_term x u t)
  | AAlways' A => AAlways' (replace_assertion_term x u A)
  | AAlwaysP' A => AAlwaysP' (replace_assertion_term x u A)
  | AEventually' A => AEventually' (replace_assertion_term x u A)
  | AEventuallyP' A => AEventuallyP' (replace_assertion_term x u A)
  | ANext A => ANext (replace_assertion_term x u A)
  | APrevious A => APrevious (replace_assertion_term x u A)
  | ASelf A => ASelf (replace_assertion_term x u A)
  end.

(* Replace all instances of variable x with term u within A *)
Definition replace_assertion_var x u A := replace_assertion_term (TVariable x) u A.

(* Extract the antecedent and consequent from an implication
 * Returns the antecedent, consequent, number of outer universal
 * quantifications, and implication constructor.  For example, if the
 * implication is weak (p -> q), the constructor is AIf.  If the
 * implication is strong (p =>> q), the constructor is AEntails.
 *)
Fixpoint extract_implication A :=
  match A with
  | AForAll A =>
    z <- extract_implication A; let '(n, c, H, A) := z in
    pure (n.+1, c, H, A)
  | ANot (AAnd (ANot (ANot H)) (ANot A)) =>
    pure (0, AIf, H, A)
  | AAnd
      (ANot (AAnd (ANot (ANot A1)) (ANot A2)))
      (ANot (AAnd (ANot (ANot A2')) (ANot A1'))) =>
    if (A1 == A1') && (A2 == A2') then pure (0, AIff, A1, A2)
    else None
  | AAnd
      (ANot (AAnd (ANot (ANot H)) (ANot A)))
      (AAlways' (ANot (AAnd (ANot (ANot H')) (ANot A')))) =>
    if (H == H') && (A == A') then pure (0, AEntails, H, A)
    else None
  | AAnd
      (AAnd
        (ANot (AAnd (ANot (ANot H1)) (ANot A1)))
        (ANot (AAnd (ANot (ANot A1')) (ANot H1'))))
     (AAlways'
        (AAnd
          (ANot (AAnd (ANot (ANot H2)) (ANot A2)))
          (ANot (AAnd (ANot (ANot A2')) (ANot H2'))))) =>
    if (H1 == H1') && (H1' == H2) && (H2 == H2') &&
       (A1 == A1') && (A1' == A2) && (A2 == A2') then
      pure (0, ACongruent, H1, A1)
    else None
  | _ => None
  end.

(* Split an implication into its antecedent and consequent
 * Returns the antecedent, consequent, and implication constructor.
 * The antecedent and consequent have the same quantifiers as A.
 *)
Definition split_implication A :=
  z <- extract_implication A; let '(n, c, H, A) := z in
  pure (c, iter n AForAll H, iter n AForAll A).

(* Form an implication from an antecedent, consequent, and constructor
 * Shared quantifiers are merged at the top level.
 *)
Fixpoint join_implication c H A :=
  match H, A with
  | AForAll H, AForAll A =>
    AForAll (join_implication c H A)
  | H, A => c H A
  end.

(* Joining a split implication yields the original implication *)
Lemma join_split_implication A' c H A :
  split_implication A' = Some (c, H, A) ->
  join_implication c H A = A'.
Proof.
Admitted.

(* Unify two assertions within an argument map
 * If the two assertions are equal when substituting according to the map,
 * an updated map is returned.
 *)
Fixpoint unify_assertion_with A' A us :=
  match A', A with
  | AFalse, AFalse => Some us
  | APredicate p', APredicate p => unify_predicate_with p' p us
  | ANot A', ANot A => unify_assertion_with A' A us
  | AAnd A'1 A'2, AAnd A1 A2 =>
    us <- unify_assertion_with A'1 A1 us;
    unify_assertion_with A'2 A2 us
  | AForAll A', AForAll A =>
    us <- unify_assertion_with A' A (push_argument_map us);
    pure (pop_argument_map us).1
  | AApplication A' t', AApplication A t =>
    us <- unify_assertion_with A' A us;
    unify_term_with t' t us
  | AAlways' A', AAlways' A => unify_assertion_with A' A us
  | AAlwaysP' A', AAlwaysP' A => unify_assertion_with A' A us
  | AEventually' A', AEventually' A => unify_assertion_with A' A us
  | AEventuallyP' A', AEventuallyP' A => unify_assertion_with A' A us
  | ANext A', ANext A => unify_assertion_with A' A us
  | APrevious A', APrevious A => unify_assertion_with A' A us
  | ASelf A', ASelf A => unify_assertion_with A' A us
  | _, _ => None
  end.

Fixpoint unify_assertion_rec A' A us :=
  if A' is AForAll A' then
    unify_assertion_rec A' A ((push_argument_map us) {= P 0 0 := None})
  else unify_assertion_with A' A us.

Definition unify_assertion A' A :=
  am <- unify_assertion_rec A' A [::];
  flatten_argument_map am.

(* Find the first subterm of A that unifies with A' *)
Fixpoint unify_sub_assertion A' A :=
  if unify_assertion A' A is Some uss then Some uss
  else
    match A with
    | AFalse => None
    | APredicate _ => None
    | ANot A => unify_sub_assertion A' A
    | AAnd A1 A2 =>
      if unify_sub_assertion A' A1 is Some uss then Some uss
      else unify_sub_assertion A' A2
    | AForAll A => unify_sub_assertion A' A
    | AApplication A _ => unify_sub_assertion A' A
    | AAlways' A => unify_sub_assertion A' A
    | AAlwaysP' A => unify_sub_assertion A' A
    | AEventually' A => unify_sub_assertion A' A
    | AEventuallyP' A => unify_sub_assertion A' A
    | ANext A => unify_sub_assertion A' A
    | APrevious A => unify_sub_assertion A' A
    | ASelf A => unify_sub_assertion A' A
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
