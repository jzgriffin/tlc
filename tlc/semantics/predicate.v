Require Import mathcomp.ssreflect.eqtype.
Require Import mathcomp.ssreflect.seq.
Require Import mathcomp.ssreflect.ssrbool.
Require Import mathcomp.ssreflect.ssreflect.
Require Import tlc.semantics.environment.
Require Import tlc.semantics.term.
Require Import tlc.syntax.all_syntax.
Require Import tlc.utility.monad.
Require Import tlc.utility.result.
Require Import tlc.utility.set.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Substitutes free variables in predicate p with terms from environment E *)
Reserved Notation "p [p/ E ]" (at level 1, left associativity).
Fixpoint substitute_predicate (E : environment) p :=
  match p with
  | PFalse => PFalse
  | PEqual tl tr => PEqual tl[t/E] tr[t/E]
  | PIn t ts => PIn t[t/E] ts[t/E]
  | PCorrect tn => PCorrect tn[t/E]
  end
where "p [p/ E ]" := (substitute_predicate E p).

(* Computes the set of free variables in a predicate *)
Fixpoint predicate_free p :=
  match p with
  | PFalse => [::]
  | PEqual tl tr => term_free tl \union term_free tr
  | PIn t ts => term_free t \union term_free ts
  | PCorrect tn => term_free tn
  end.

(* Evaluates a predicate as far as possible
 * This process produces an assertion instead of a predicate *)
Fixpoint evaluate_predicate p :=
  match p with
  | PFalse => pure AFalse
  | PEqual tl tr =>
    tl <- evaluate_term tl;
    tr <- evaluate_term tr;
    if tl == tr then pure ATrue else pure AFalse
  | PIn t ts =>
    t <- evaluate_term t;
    ts <- evaluate_term ts;
    ts <- lift_list ts;
    if t \in ts then pure ATrue else pure AFalse
  | PCorrect tn =>
    tn <- evaluate_term tn;
    pure (AIn tn "Correct")
  end.
Notation "[[p p ]]" := (evaluate_predicate p) (at level 0, no associativity).

(* Tactic for evaluation *)
Ltac evaluate_predicate := rewrite /evaluate_predicate /=.
