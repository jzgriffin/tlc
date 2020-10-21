(* TLC in Coq
 *
 * Module: tlc.semantics.pattern
 * Purpose: Contains the pattern matching algorithm.
 *)

Require Import mathcomp.ssreflect.eqtype.
Require Import mathcomp.ssreflect.path.
Require Import mathcomp.ssreflect.seq.
Require Import mathcomp.ssreflect.ssrbool.
Require Import mathcomp.ssreflect.ssreflect.
Require Import mathcomp.ssreflect.ssrfun.
Require Import mathcomp.ssreflect.ssrnat.
Require Import tlc.syntax.all_syntax.
Require Import tlc.utility.monad.
Require Import tlc.utility.option.
Require Import tlc.utility.partial_map.
Require Import tlc.utility.result.
Require Import tlc.utility.seq.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Errors that may be encountered while operating on patterns *)
Inductive pattern_error :=
| PEIll (p : pattern)
| PEParameter (j : nat) (t t' : term)
| PEConstructor (cp ct : constructor)
| PEStructure (p : pattern) (t : term).

(* Compute the set of parameters appearing in a pattern *)
Fixpoint pattern_params p :=
  match p with
  | PWildcard => [::]
  | PParameter j => [:: j]
  | PConstructor _ => [::]
  | PApplication f a => union (pattern_params f) (pattern_params a)
  end.

(* Compute the arity (number of parameters) in a pattern *)
Definition pattern_arity p :=
  let xs := pattern_params p in
  if nilp xs then 0 else (foldr maxn 0 xs).+1.

(* Determine whether a pattern is well-formed
 * Well-formed patterns are those whose set of used parameters is equal to the
 * set {j | j < |p|}.
 *)
Definition pattern_wf p :=
  set_eq (pattern_params p) (iota 0 (pattern_arity p)).

(* Match a term t against a pattern p and return the map of terms bound by p *)
Fixpoint match_pattern_rec p t (m : partial_map [eqType of nat] term) :=
  match p, t with
  | PWildcard, _ => pure m
  | PParameter j, t =>
    if m{@j} is Some t'
    then if t == t' then pure m else Failure (PEParameter j t t')
    else pure m{= j := t}
  | PConstructor cp, TConstructor ct =>
    if cp == ct then pure m
    else Failure (PEConstructor cp ct)
  | PApplication pf pa, TApplication tf ta =>
    m' <- match_pattern_rec pf tf m;
    match_pattern_rec pa ta m'
  | _, _ => Failure (PEStructure p t)
  end.

(* Match a term t against a pattern p and return the list of terms bound by p *)
Definition match_pattern p t :=
  if pattern_wf p then
    m <- match_pattern_rec p t [::];
    pure (map snd (sort (fun '(j1, _) '(j2, _) => j1 <= j2) m))
  else Failure (PEIll p).

(* Construct a term that will match a pattern
 * Each pattern wildcard and parameter is represented as a parameter in the
 * resulting term.  The term parameters are each produced on a separate binding
 * level.  For pattern parameters, the resulting term parameter is bound at the
 * level of the index of the pattern parameter.  Pattern wildcards are bound at
 * the levels above the arity of the pattern, in the order in which they are
 * encountered.
 *)
Fixpoint pattern_term_rec p n :=
  match p with
  | PWildcard => (TParameter (P n 0), n.+1)
  | PParameter j => (TParameter (P j 0), n)
  | PConstructor c => (TConstructor c, n)
  | PApplication pf pa =>
    let '(tf, n) := pattern_term_rec pf n in
    let '(ta, n) := pattern_term_rec pa n in
    (TApplication tf ta, n)
  end.
Definition pattern_term p :=
  if pattern_wf p
  then Some (pattern_term_rec p (pattern_arity p))
  else None.
Example pattern_term_1 :
  pattern_term {-p ($1, %, $0, $1) -} =
  Some ({-t ($(1, 0), $(2, 0), $(0, 0), $(1, 0)) -}, 3).
by []. Defined.

(* Destruct a case of an argument term into an assertion about that term when
 * it satisfies the case
 * A term that matches the case pattern is constructed using pattern_term.
 * That term is then equated to the argument term and the equality is wrapped
 * in N existential quantifiers, where N is the number of bindings in the
 * pattern term.
 *)
Definition destruct_case a (c : match_case) :=
  let '(p, b) := c in
  ts <- pattern_term p;
  let '(t, n) := ts in
  pure (iter n AExists {-A a = t -}).

(* Destruct a list of cases of an argument term into an assertion about that
 * term when it satisfies at least one of the cases
 *)
Fixpoint destruct_cases a (cs : match_cases) :=
  match cs with
  | nil => pure ATrue
  | [:: c] => destruct_case a c
  | c :: cs =>
    A <- destruct_case a c;
    As <- destruct_cases a cs;
    pure (AOr A As)
  end.
