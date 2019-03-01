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
    | AAnd Al Ar => AAnd (f Al n) (f Ar n)
    | AForAll v A => AForAll v (f A n)
    | AAlways' A => AAlways' (f A n)
    | AAlwaysP' A => AAlwaysP' (f A n)
    | AEventually' A => AEventually' (f A n)
    | AEventuallyP' A => AEventuallyP' (f A n)
    | ANext A => ANext (f A n)
    | APrevious A => APrevious (f A n)
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
    | AAnd Al Ar => AAnd (f Al) (f Ar)
    | AForAll v A => AForAll v (f A)
    | AAlways' A => AAlways' (f A)
    | AAlwaysP' A => AAlwaysP' (f A)
    | AEventually' A => AEventually' (f A)
    | AEventuallyP' A => AEventuallyP' (f A)
    | ANext A => ANext (f A)
    | APrevious A => APrevious (f A)
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
  | AAnd Al Ar => AAnd (Al /A/ e) (Ar /A/ e)
  | AForAll v A => AForAll v (A /A/ e{-(TVariable v)})
  | AAlways' A => AAlways' (A /A/ e)
  | AAlwaysP' A => AAlwaysP' (A /A/ e)
  | AEventually' A => AEventually' (A /A/ e)
  | AEventuallyP' A => AEventuallyP' (A /A/ e)
  | ANext A => ANext (A /A/ e)
  | APrevious A => APrevious (A /A/ e)
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
  | AAnd Al Ar => assertion_free Al \union assertion_free Ar
  | AForAll v A => rem v (assertion_free A)
  | AAlways' A => assertion_free A
  | AAlwaysP' A => assertion_free A
  | AEventually' A => assertion_free A
  | AEventuallyP' A => assertion_free A
  | ANext A => assertion_free A
  | APrevious A => assertion_free A
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
  | AAnd Al Ar =>
    Al <- [[A Al]];
    Ar <- [[A Ar]];
    pure (AAnd Al Ar)
  | AForAll v A =>
    A <- [[A A]];
    pure (AForAll v A)
  | AAlways' A =>
    A <- [[A A]];
    pure (AAlways' A)
  | AAlwaysP' A =>
    A <- [[A A]];
    pure (AAlwaysP' A)
  | AEventually' A =>
    A <- [[A A]];
    pure (AEventually' A)
  | AEventuallyP' A =>
    A <- [[A A]];
    pure (AEventuallyP' A)
  | ANext A =>
    A <- [[A A]];
    pure (ANext A)
  | APrevious A =>
    A <- [[A A]];
    pure (APrevious A)
  | ASelf A =>
    A <- [[A A]];
    pure (ASelf A)
  end
where "[[A A ]]" := (evaluate_assertion A).

(* Tactic for evaluation *)
Ltac evaluate_assertion := rewrite /evaluate_assertion /=; evaluate_predicate.
