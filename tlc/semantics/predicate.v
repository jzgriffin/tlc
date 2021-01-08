(* TLC in Coq
 *
 * Module: tlc.semantics.predicate
 * Purpose: Contains the semantics for predicate forms.
 *)

Require Import mathcomp.ssreflect.eqtype.
Require Import mathcomp.ssreflect.ssrbool.
Require Import mathcomp.ssreflect.ssreflect.
Require Import mathcomp.ssreflect.seq.
Require Import tlc.semantics.term.
Require Import tlc.syntax.all_syntax.
Require Import tlc.utility.monad.
Require Import tlc.utility.result.
Require Import tlc.utility.seq.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition push_predicate_params_rec p k :=
  match p with
  | PEqual x1 x2 =>
    PEqual
      (push_term_params_rec x1 k)
      (push_term_params_rec x2 k)
  | PLess x1 x2 =>
    PLess
      (push_term_params_rec x1 k)
      (push_term_params_rec x2 k)
  | PMember y xs =>
    PMember
      (push_term_params_rec y k)
      (push_term_params_rec xs k)
  | PExtension xs' xs =>
    PExtension
      (push_term_params_rec xs' k)
      (push_term_params_rec xs k)
  end.

Definition push_predicate_params p := push_predicate_params_rec p 0.

(* Unify two predicates within an argument map
 * If the two predicates are equal when substituting according to the map,
 * an updated map is returned.
 *)
Definition unify_predicate_with p' p us :=
  match p', p with
  | PEqual x'1 x'2, PEqual x1 x2
  | PLess x'1 x'2, PLess x1 x2
  | PMember x'1 x'2, PMember x1 x2
  | PExtension x'1 x'2, PExtension x1 x2 =>
    us <- unify_term_with x'1 x1 us;
    unify_term_with x'2 x2 us
  | _, _ => None
  end.

(* Open a predicate p at depth k with bindings us *)
Definition open_predicate_at k us p :=
  match p with
  | PEqual x1 x2 =>
    x1 <- open_term_at k us x1;
    x2 <- open_term_at k us x2;
    pure (PEqual x1 x2)
  | PLess x1 x2 =>
    x1 <- open_term_at k us x1;
    x2 <- open_term_at k us x2;
    pure (PLess x1 x2)
  | PMember y xs =>
    y <- open_term_at k us y;
    xs <- open_term_at k us xs;
    pure (PMember y xs)
  | PExtension xs' xs =>
    xs' <- open_term_at k us xs';
    xs <- open_term_at k us xs;
    pure (PExtension xs' xs)
  end.
Definition open_predicate := open_predicate_at 0.

(* Determine whether a predicate is locally closed
 * A predicate is locally closed if every parameter reference is well-formed.
 *)
Definition predicate_lc_in ks p :=
  match p with
  | PEqual x1 x2 => term_lc_in ks x1 && term_lc_in ks x2
  | PLess x1 x2 => term_lc_in ks x1 && term_lc_in ks x2
  | PMember y xs => term_lc_in ks y && term_lc_in ks xs
  | PExtension xs' xs => term_lc_in ks xs' && term_lc_in ks xs
  end.
Definition predicate_lc := predicate_lc_in [::].

(* Any predicate that is closed at depth ks is closed at depth k :: ks *)
Lemma predicate_lc_in_cons k ks p :
  predicate_lc_in ks p ->
  predicate_lc_in (k :: ks) p.
Proof.
Admitted.

(* Any predicate that is closed at depth ks is closed at depth ks' ++ ks *)
Lemma predicate_lc_in_concat ks' ks p :
  predicate_lc_in ks p ->
  predicate_lc_in (ks' ++ ks) p.
Proof.
  elim: ks' => [| k ks' IH] //=.
  by move=> H; specialize (IH H); apply predicate_lc_in_cons.
Qed.

(* Opening a closed predicate at a depth above its closure depth has no effect *)
Lemma open_lc_predicate_at k ks us p :
  k >= size ks ->
  predicate_lc_in ks p ->
  open_predicate_at k us p = Success p.
Proof.
Admitted.

(* Compute the set of flexible variables appearing in a predicate *)
Definition predicate_flexibles p :=
  match p with
  | PEqual x1 x2 => term_flexibles x1 ++ term_flexibles x2
  | PLess x1 x2 => term_flexibles x1 ++ term_flexibles x2
  | PMember y xs => term_flexibles y ++ term_flexibles xs
  | PExtension xs' xs => term_flexibles xs' ++ term_flexibles xs
  end.

(* Compute the set of rigid variables appearing in a predicate *)
Definition predicate_rigids p :=
  match p with
  | PEqual x1 x2 => term_rigids x1 ++ term_rigids x2
  | PLess x1 x2 => term_rigids x1 ++ term_rigids x2
  | PMember y xs => term_rigids y ++ term_rigids xs
  | PExtension xs' xs => term_rigids xs' ++ term_rigids xs
  end.

(* Compute the set of variables appearing in a predicate *)
Definition predicate_vars p :=
  map VF (predicate_flexibles p) ++ map VR (predicate_rigids p).

(* Determine whether a predicate is globally closed
 * A predicate is globally closed if it contains no rigid variables.
 *)
Definition predicate_gc_in xs p := subset (predicate_rigids p) xs.
Definition predicate_gc := predicate_gc_in [::].

(* Determine whether a predicate is closed
 * A predicate is closed if it is locally and globally closed.
 *)
Definition predicate_closed_in ks xs p :=
  predicate_lc_in ks p && predicate_gc_in xs p.
Definition predicate_closed p := predicate_lc p && predicate_gc p.

(* A closed predicate is locally closed *)
Lemma closed_predicate_lc ks xs p :
  predicate_closed_in ks xs p ->
  predicate_lc_in ks p.
Proof.
  by move/andP => [??].
Qed.

(* A closed predicate is globally closed *)
Lemma closed_predicate_gc ks xs p :
  predicate_closed_in ks xs p ->
  predicate_gc_in xs p.
Proof.
  by move/andP => [??].
Qed.

(* Well-formed opening will not fail *)
Lemma open_closed_predicate_at ks xs k us p :
  predicate_closed_in ks xs p ->
  onth ks k = Some (size us) ->
  exists p', open_predicate_at k us p = Success p'.
Proof.
Admitted.

(* Determine whether a predicate is rigid
 * A predicate is rigid if it contains no flexible variables.
 *)
Definition predicate_rigid p :=
  match p with
  | PEqual x1 x2 => term_rigid x1 && term_rigid x2
  | PLess x1 x2 => term_rigid x1 && term_rigid x2
  | PMember y xs => term_rigid y && term_rigid xs
  | PExtension xs' xs => term_rigid xs' && term_rigid xs
  end.

(* Replace all instances of term x with term u within p *)
Definition replace_predicate_term x u p :=
  match p with
  | PEqual x1 x2 => PEqual (replace_term x u x1) (replace_term x u x2)
  | PLess x1 x2 => PLess (replace_term x u x1) (replace_term x u x2)
  | PMember y xs => PMember (replace_term x u y) (replace_term x u xs)
  | PExtension xs' xs =>
    PExtension (replace_term x u xs') (replace_term x u xs)
  end.

(* Replace all instances of variable x with term u within p *)
Definition replace_predicate_var x u p := replace_predicate_term (TVariable x) u p.

(* Reduce the subterms of predicate P *)
Definition reduce_predicate p :=
  match p with
  | PEqual x1 x2 =>
    x1 <- [[t x1]];
    x2 <- [[t x2]];
    pure (PEqual x1 x2)
  | PLess x1 x2 =>
    x1 <- [[t x1]];
    x2 <- [[t x2]];
    pure (PLess x1 x2)
  | PMember y xs =>
    y <- [[t y]];
    xs <- [[t xs]];
    pure (PMember y xs)
  | PExtension xs' xs =>
    xs' <- [[t xs']];
    xs <- [[t xs]];
    pure (PExtension xs' xs)
  end.
Notation "[[P p ]]" := (reduce_predicate p) (at level 0, no associativity).
