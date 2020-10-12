(* TLC in Coq
 *
 * Module: tlc.semantics.tactics
 * Purpose: Contains tactics related to the semantics of terms and assertions.
 *)

Require Import mathcomp.ssreflect.eqtype.
Require Import mathcomp.ssreflect.seq.
Require Import mathcomp.ssreflect.ssrbool.
Require Import mathcomp.ssreflect.ssreflect.
Require Import tlc.semantics.assertion.
Require Import tlc.semantics.predicate.
Require Import tlc.semantics.term.
Require Import tlc.syntax.all_syntax.
Require Import tlc.utility.result.
Require Import tlc.utility.seq.

(* Tactics for refolding syntactic sugar *)
Ltac dclean :=
  dfold_assertion.

(*
(* Tactics for distinguishing variables *)
Ltac distinguish_variable x y Hf :=
  let H := fresh "H" in
  assert (H: ((x == y) = false)); [
    by apply negbTE; eapply eq_notin; last first; [apply Hf | repeat auto_in_seq] ||
    by rewrite eq_sym; apply negbTE; eapply eq_notin; last first; [apply Hf | repeat auto_in_seq]
  | rewrite {}H
  ].
Ltac distinguish_variables :=
  repeat match goal with
  | [ Hf: is_true (_ \notin _) |- context[ eq_op ?x ?y ] ] =>
    distinguish_variable x y Hf
  | [ Hf: is_true (_ \notin _) |- context[ variable_eq ?x ?y ] ] =>
    rewrite -!eqE; distinguish_variable x y Hf
  end; rewrite /=.
*)

(* Tactics for automatically solving openings *)
Ltac dautoclosed :=
  match goal with
  | |- is_true (assertion_lc_in ?ks ?A) =>
    (try by []);
    (try by apply: closed_assertion_lc);
    (try by match goal with
    | Hc : is_true (assertion_closed_in ?ks _ A) |- _ =>
      apply: closed_assertion_lc; exact: Hc
    end)
  | |- is_true (assertion_closed_in _ _ _) =>
    (try by []);
    (try by rewrite /assertion_closed_in /= /assertion_gc_in /assertion_lc_in /=
      ?andbT ?andTb; auto_mem_conj)

  | |- is_true (predicate_lc_in ?ks ?p) =>
    (try by []);
    (try by apply: closed_predicate_lc);
    (try by match goal with
    | Hc : is_true (assertion_closed_in ?ks _ p) |- _ =>
      apply: closed_predicate_lc; exact: Hc
    end)
  | |- is_true (predicate_closed_in _ _ _) =>
    (try by []);
    (try by rewrite /predicate_closed_in /= /predicate_gc_in /predicate_lc_in /=
      ?andbT ?andTb; auto_mem_conj)

  | |- is_true (term_lc_in ?ks ?t) =>
    (try by []);
    (try by apply: closed_term_lc);
    (try by apply: closed_term_lc; apply: computable_term_closed);
    (try by match goal with
    | Hc : is_true (term_closed_in ?ks _ t) |- _ =>
      apply: closed_term_lc; exact: Hc
    end)
  | |- is_true (term_closed_in _ _ _) =>
    (try by []);
    (try by apply: computable_term_closed);
    (try by rewrite /term_closed_in /= /term_gc_in /term_lc_in /=
      ?andbT ?andTb; auto_mem_conj)
  end.

Ltac dautoopen :=
  rewrite
    /open_assertion /=
    /open_predicate /=
    /open_term /=
    -/open_term_at
    -/open_predicate_at
    -/open_assertion_at;
  repeat match goal with
  | |- context[ open_assertion_at ?k ?us ?A ] =>
    let H := fresh "H" in
    assert (H : open_assertion_at k us A = Success A);
    [eapply (@open_lc_assertion_at k _ us A); last first;
      [dautoclosed | try by [] ] |
    rewrite {}H]
  | |- context[ open_predicate_at ?k ?us ?p ] =>
    let H := fresh "H" in
    assert (H : open_predicate_at k us p = Success p);
    [eapply (@open_lc_predicate_at k _ us p); last first;
      [dautoclosed | try by [] ] |
    rewrite {}H]
  | |- context[ open_term_at ?k ?us ?t ] =>
    let H := fresh "H" in
    assert (H : open_term_at k us t = Success t);
    [eapply (@open_lc_term_at k _ us t); last first;
      [dautoclosed | try by [] ] |
    rewrite {}H]
  end.
