(* TLC in Coq
 *
 * Module: tlc.semantics.predicate
 * Purpose: Contains the semantics for predicate forms.
 *)

Require Import mathcomp.ssreflect.eqtype.
Require Import mathcomp.ssreflect.seq.
Require Import mathcomp.ssreflect.ssrbool.
Require Import mathcomp.ssreflect.ssreflect.
Require Import tlc.semantics.environment.
Require Import tlc.semantics.equivalents.
Require Import tlc.semantics.term.
Require Import tlc.syntax.all_syntax.
Require Import tlc.utility.monad.
Require Import tlc.utility.result.
Require Import tlc.utility.set.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Substitutes terms in predicate p with terms from a equivalence map e *)
Definition substitute_predicate (e : equivalents) p :=
  match p with
  | PFalse => p
  | PEqual tl tr => PEqual (tl /t/ e) (tr /t/ e)
  | PIn t ts => PIn (t /t/ e) (ts /t/ e)
  | PExtension ts' ts => PExtension (ts' /t/ e) (ts /t/ e)
  | PCorrect tn => PCorrect (tn /t/ e)
  end.
Notation "p /p/ e" := (substitute_predicate e p)
  (at level 40, left associativity).

(* Substitutes free variables in a predicate p with terms from environment e
 * NOTE: This process is not capture-avoiding.
 *)
Definition instantiate_predicate (e : environment) p :=
  p /p/ environment_equivalents e.

(* Computes the set of free variables in a predicate *)
Fixpoint predicate_free p :=
  match p with
  | PFalse => [::]
  | PEqual tl tr => term_free tl \union term_free tr
  | PIn t ts => term_free t \union term_free ts
  | PExtension ts' ts => term_free ts' \union term_free ts
  | PCorrect tn => term_free tn
  end.

(* Evaluates the subterms of predicate p *)
Reserved Notation "[[p p ]]" (at level 0, no associativity).
Fixpoint evaluate_predicate p :=
  match p with
  | PFalse => pure PFalse
  | PEqual tl tr =>
    tl <- [[t tl]];
    tr <- [[t tr]];
    pure (PEqual tl tr)
  | PIn t ts =>
    t <- [[t t]];
    ts <- [[t ts]];
    pure (PIn t ts)
  | PExtension ts' ts =>
    ts' <- [[t ts']];
    ts <- [[t ts]];
    pure (PExtension ts' ts)
  | PCorrect tn =>
    tn <- [[t tn]];
    pure (PCorrect tn)
  end
where "[[p p ]]" := (evaluate_predicate p).

(* Tactics for semantic operations on predicates *)
Ltac substitute_predicate :=
  rewrite /substitute_predicate /=;
  substitute_term.
Ltac instantiate_predicate :=
  rewrite /instantiate_predicate /=;
  instantiate_term.
Ltac evaluate_predicate :=
  rewrite /evaluate_predicate /=;
  evaluate_term.
