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

(* Automatically resolve known equalities *)
Ltac dautoeq :=
  rewrite ?eqE /= -?eqE ?rigid_eqE;
  repeat match goal with
  | H : ?x <> ?y |- context[ ?x == ?y ] =>
    rewrite (negbTE (introN eqP H))
  | H : ?y <> ?x |- context[ ?x == ?y ] =>
    rewrite (negbTE (introN eqP (not_eq_sym H)))
  end;
  rewrite ?eq_refl ?andbT ?andTb ?andbF ?andFb /=.

(* Automatically simplify replacement *)
Ltac dreplace :=
  rewrite
    /replace_assertion_var
    /replace_predicate_var
    /replace_term_var
    /replace_assertion_term
    /replace_predicate_term
    /replace_term
    /=
    -/replace_term
    -/replace_predicate_term
    -/replace_assertion_term
    -/replace_term_var
    -/replace_predicate_var
    -/replace_assertion_var
    ?replace_rigid_term_flexible_var
    ?replace_gc_term_rigid_var
    ?eq_refl;
    (try by exact: computable_term_rigid);
    (try by exact: computable_term_closed);
  dautoeq;
  rewrite ?eq_refl ?andbF ?andFb.

(* Tactics for refolding syntactic sugar *)
Ltac dclean :=
  dreplace; dfold_assertion.

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
  | |- is_true (assertion_closed_in _ _ ?A) =>
    (try by []);
    (try by rewrite /assertion_closed_in /= /assertion_gc_in /assertion_lc_in /=
      ?andbT ?andTb; auto_mem_conj);
    (try by match goal with
    | Hc : is_true (assertion_closed_in _ _ A) |- _ => eapply Hc
    end)

  | |- is_true (predicate_lc_in ?ks ?p) =>
    (try by []);
    (try by apply: closed_predicate_lc);
    (try by match goal with
    | Hc : is_true (assertion_closed_in ?ks _ p) |- _ =>
      apply: closed_predicate_lc; exact: Hc
    end)
  | |- is_true (predicate_closed_in _ _ ?p) =>
    (try by []);
    (try by rewrite /predicate_closed_in /= /predicate_gc_in /predicate_lc_in /=
      ?andbT ?andTb; auto_mem_conj);
    (try by match goal with
    | Hc : is_true (predicate_closed_in _ _ p) |- _ => eapply Hc
    end)

  | |- is_true (term_lc_in ?ks ?t) =>
    (try by []);
    (try by apply: closed_term_lc);
    (try by apply: closed_term_lc; apply: computable_term_closed);
    (try by match goal with
    | Hc : is_true (term_closed_in ?ks _ t) |- _ =>
      apply: closed_term_lc; exact: Hc
    end)
  | |- is_true (term_closed_in _ _ ?t) =>
    (try by []);
    (try by apply: computable_term_closed);
    (try by rewrite /term_closed_in /= /term_gc_in /term_lc_in /=
      ?andbT ?andTb; auto_mem_conj);
    (try by match goal with
    | Hc : is_true (term_closed_in _ _ t) |- _ => eapply Hc
    end)
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
  | |- context[ open_assertion_at ?k ?us ?A ] =>
    let H := fresh "H" in
    let A' := fresh A "'" in
    assert (H : exists A', open_assertion_at k us A = Success A');
      [by eapply open_closed_assertion_at; [dautoclosed |] |
      case: H => A' ->]

  | |- context[ open_predicate_at ?k ?us ?p ] =>
    let H := fresh "H" in
    assert (H : open_predicate_at k us p = Success p);
    [eapply (@open_lc_predicate_at k _ us p); last first;
      [dautoclosed | try by [] ] |
    rewrite {}H]
  | |- context[ open_predicate_at ?k ?us ?p ] =>
    let H := fresh "H" in
    let p' := fresh p "'" in
    assert (H : exists p', open_predicate_at k us p = Success p');
      [by eapply open_closed_predicate_at; [dautoclosed |] |
      case: H => p' ->]

  | |- context[ open_term_at ?k ?us ?t ] =>
    let H := fresh "H" in
    assert (H : open_term_at k us t = Success t);
    [eapply (@open_lc_term_at k _ us t); last first;
      [dautoclosed | try by [] ] |
    rewrite {}H]
  | |- context[ open_term_at ?k ?us ?t ] =>
    let H := fresh "H" in
    let t' := fresh t "'" in
    assert (H : exists t', open_term_at k us t = Success t');
      [by eapply open_closed_term_at; [dautoclosed |] |
      case: H => t' ->]
  end.
