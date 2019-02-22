Require Import mathcomp.ssreflect.eqtype.
Require Import mathcomp.ssreflect.seq.
Require Import mathcomp.ssreflect.ssrbool.
Require Import mathcomp.ssreflect.ssreflect.
Require Import mathcomp.ssreflect.ssrnat.
Require Import tlc.semantics.environment.
Require Import tlc.semantics.equivalents.
Require Import tlc.semantics.predicate.
Require Import tlc.syntax.all_syntax.
Require Import tlc.utility.monad.
Require Import tlc.utility.partial_map.
Require Import tlc.utility.result.
Require Import tlc.utility.set.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Replaces positive occurrences of assertion Ap with assertion Ac in
 * assertion A.  An occurrence is positive if it appears inside an even
 * number of negations
 *)
Definition rewrite_assertion_pos Ap Ac A :=
  let fix f A n :=
    if A == Ap then if odd n then Ap else Ac else
    match A with
    | APredicate _ => A
    | ANot A => ANot (f A n.+1)
    | AOr Al Ar => AOr (f Al n) (f Ar n)
    | AForAll v A => AForAll v (f A n)
    | AUntil' Al Ar => AUntil' (f Al n) (f Ar n)
    | ASince' Al Ar => ASince' (f Al n) (f Ar n)
    | ASelf A => ASelf (f A n)
    end
  in
  f A 0.

(* Replaces all occurrences of assertion Ap with assertion Ac in
 * assertion A
 *)
Definition rewrite_assertion_any Ap Ac A :=
  let fix f A :=
    if A == Ap then Ac else
    match A with
    | APredicate _ => A
    | ANot A => ANot (f A)
    | AOr Al Ar => AOr (f Al) (f Ar)
    | AForAll v A => AForAll v (f A)
    | AUntil' Al Ar => AUntil' (f Al) (f Ar)
    | ASince' Al Ar => ASince' (f Al) (f Ar)
    | ASelf A => ASelf (f A)
    end
  in
  f A.

(* Substitutes terms in assertion A with terms from a equivalence map e *)
Reserved Notation "A /A/ e" (at level 40, left associativity).
Fixpoint substitute_assertion (e : equivalents) A :=
  match A with
  | APredicate p => APredicate (p /p/ e)
  | ANot A => ANot (A /A/ e)
  | AOr Al Ar => AOr (Al /A/ e) (Ar /A/ e)
  | AForAll v A => AForAll v (A /A/ e{-(TVariable v)})
  | AUntil' Al Ar => AUntil' (Al /A/ e) (Ar /A/ e)
  | ASince' Al Ar => ASince' (Al /A/ e) (Ar /A/ e)
  | ASelf A => ASelf (A /A/ e)
  end
where "A /A/ e" := (substitute_assertion e A).

(* Substitutes free variables in an assertion A with terms from environment e *)
Definition instantiate_assertion (e : environment) A :=
  A /A/ environment_equivalents e.

(* Computes the set of free variables in an assertion *)
Fixpoint assertion_free A :=
  match A with
  | APredicate p => predicate_free p
  | ANot A => assertion_free A
  | AOr Al Ar => assertion_free Al \union assertion_free Ar
  | AForAll v A => rem v (assertion_free A)
  | AUntil' Al Ar => assertion_free Al \union assertion_free Ar
  | ASince' Al Ar => assertion_free Al \union assertion_free Ar
  | ASelf A => assertion_free A
  end.

(* Evaluates the subterms of assertion A *)
Reserved Notation "[[A A ]]" (at level 0, no associativity).
Fixpoint evaluate_assertion A :=
  match A with
  | APredicate p =>
    p <- [[p p]];
    pure (APredicate p)
  | ANot A =>
    A <- [[A A]];
    pure (ANot A)
  | AOr Al Ar =>
    Al <- [[A Al]];
    Ar <- [[A Ar]];
    pure (AOr Al Ar)
  | AForAll v A =>
    A <- [[A A]];
    pure (AForAll v A)
  | AUntil' Al Ar =>
    Al <- [[A Al]];
    Ar <- [[A Ar]];
    pure (AUntil' Al Ar)
  | ASince' Al Ar =>
    Al <- [[A Al]];
    Ar <- [[A Ar]];
    pure (ASince' Al Ar)
  | ASelf A =>
    A <- [[A A]];
    pure (ASelf A)
  end
where "[[A A ]]" := (evaluate_assertion A).

(* Tactic for evaluation *)
Ltac evaluate_assertion := rewrite /evaluate_assertion /=; evaluate_predicate.

(* Proposition for non-temporal assertions *)
Inductive non_temporal_assertion : assertion -> Prop :=
| NTAPredicate p :
  non_temporal_assertion {A: #p}
| NTANot A :
  non_temporal_assertion A ->
  non_temporal_assertion {A: ~A}
| NTAOr Al Ar :
  non_temporal_assertion Al ->
  non_temporal_assertion Ar ->
  non_temporal_assertion {A: Al \/ Ar}
| NTAForAll v A :
  non_temporal_assertion A ->
  non_temporal_assertion {A: forall: v, A}.
