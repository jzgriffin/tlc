Require Import mathcomp.ssreflect.eqtype.
Require Import mathcomp.ssreflect.ssrbool.
Require Import mathcomp.ssreflect.ssreflect.
Require Import mathcomp.ssreflect.ssrnat.
Require Import tlc.component.component.
Require Import tlc.logic.derives.
Require Import tlc.syntax.all_syntax.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Implication rewriting *)
Lemma DRewriteIf C Gamma Ap Ac (H : Gamma |- C, {A: Ap -> Ac}) A :
  Gamma |- C, rewrite_if H A <-> Gamma |- C, A.
Proof.
Admitted. (* TODO *)

(* Equivalence rewriting *)
Lemma DRewriteIffL C Gamma Ap Ac (H : Gamma |- C, {A: Ap <-> Ac}) A :
  Gamma |- C, rewrite_iff_left H A <-> Gamma |- C, A.
Proof.
Admitted. (* TODO *)

Definition rewrite_iff_right C Gamma Ap Ac (H : Gamma |- C, {A: Ap <-> Ac}) A :=
  rewrite_iff_left (DIffCommutative H) A.

Lemma DRewriteIffR C Gamma Ap Ac (H : Gamma |- C, {A: Ap <-> Ac}) A :
  Gamma |- C, rewrite_iff_right H A <-> Gamma |- C, A.
Proof.
  by apply DRewriteIffL.
Defined.

(* Entailment rewriting *)
Fixpoint rewrite_entails C Gamma Ap Ac (H : Gamma |- C, {A: Ap =>> Ac}) A :=
  let fix rewrite_entails' A n :=
    if A == Ap then if odd n then Ap else Ac else
    match A with
    | APredicate _ => A
    | ANot A => ANot (rewrite_entails' A n.+1)
    | AOr Al Ar => AOr (rewrite_entails' Al n) (rewrite_entails' Ar n)
    | AForAll v A => AForAll v (rewrite_entails' A n)
    | AUntil' Al Ar => AUntil' (rewrite_entails' Al n) (rewrite_entails' Ar n)
    | ASince' Al Ar => ASince' (rewrite_entails' Al n) (rewrite_entails' Ar n)
    | ASelf A => ASelf (rewrite_entails' A n)
    end
  in
  rewrite_entails' A 0.

Lemma rewrite_entails_correct C Gamma Ap Ac (H : Gamma |- C, {A: Ap =>> Ac}) A :
  Gamma |- C, rewrite_entails H A <-> Gamma |- C, A.
Proof.
Admitted. (* TODO *)

Lemma rewrite_entails_correct_inline C Gamma Ap Ac A :
  {A: Ap =>> Ac} :: Gamma |- C, rewrite_entails (DSAxiom C ({A: Ap =>> Ac} :: Gamma)
    {A: Ap =>> Ac}) A <-> {A: Ap =>> Ac} :: Gamma |- C, A.
Proof.
Admitted. (* TODO *)

(* Congruence rewriting *)
Fixpoint rewrite_congruent_left C Gamma Ap Ac (H : Gamma |- C, {A: Ap <=> Ac}) A :=
  if A == Ap then Ac else
  match A with
  | APredicate _ => A
  | ANot A => ANot (rewrite_congruent_left H A)
  | AOr Al Ar => AOr
    (rewrite_congruent_left H Al)
    (rewrite_congruent_left H Ar)
  | AForAll v A => AForAll v (rewrite_congruent_left H A)
  | AUntil' Al Ar => AUntil'
    (rewrite_congruent_left H Al)
    (rewrite_congruent_left H Ar)
  | ASince' Al Ar => ASince'
    (rewrite_congruent_left H Al)
    (rewrite_congruent_left H Ar)
  | ASelf A => ASelf (rewrite_congruent_left H A)
  end.

Fixpoint appears_in Ap A :=
  if A == Ap then true else
  match A with
  | APredicate _ => false
  | ANot A => appears_in Ap A
  | AOr Al Ar => appears_in Ap Al || appears_in Ap Ar
  | AForAll v A => appears_in Ap A
  | AUntil' Al Ar => appears_in Ap Al || appears_in Ap Ar
  | ASince' Al Ar => appears_in Ap Al || appears_in Ap Ar
  | ASelf A => appears_in Ap A
  end.

Lemma rewrite_congruent_left_correct C Gamma Ap Ac (H : Gamma |- C, {A: Ap <=> Ac})
  A : Gamma |- C, rewrite_congruent_left H A <-> Gamma |- C, A.
Proof.
Admitted. (* TODO *)

Definition rewrite_congruent_right C Gamma Ap Ac (H : Gamma |- C, {A: Ap <=> Ac}) A
  := rewrite_congruent_left (DCongruentCommutative H) A.

Lemma rewrite_congruent_right_correct C Gamma Ap Ac (H : Gamma |- C, {A: Ap <=> Ac})
  A : Gamma |- C, rewrite_congruent_right H A <-> Gamma |- C, A.
Proof.
  by apply rewrite_congruent_left_correct.
Defined.
