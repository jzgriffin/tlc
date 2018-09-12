From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat.
From Coq.Program
Require Import Program.

Require Import all_assert.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Program Fixpoint restrict (e' e : InterleavableAssertionT)
  {measure (assertion_height (projT1 e))} : InterleavableAssertionT :=
  match e', e with existT A' IA', existT A IA =>
    match IA with
    | Interleavable_false =>
      existT Interleavable
        Afalse
        Interleavable_false
    | Interleavable_pred p ts =>
      existT Interleavable
        (Apred p ts)
        (Interleavable_pred p ts)
    | Interleavable_conj A1 A2 IA1 IA2 =>
      let: e1 := existT Interleavable A1 IA1 in
      let: e2 := existT Interleavable A2 IA2 in
      let: er1 := restrict e' e1 in
      let: er2 := restrict e' e2 in
      existT Interleavable
        (Aconj (projT1 er1) (projT1 er2))
        (Interleavable_conj (projT2 er1) (projT2 er2))
    | Interleavable_neg A0 IA0 =>
      let: e0 := existT Interleavable A0 IA0 in
      let: er0 := restrict e' e0 in
      existT Interleavable
        (Aneg (projT1 er0))
        (Interleavable_neg (projT2 er0))
    | Interleavable_univ x A0 IA0 =>
      let: e0 := existT Interleavable A0 IA0 in
      let: er0 := restrict e' e0 in
      existT Interleavable
        (Auniv x (projT1 er0))
        (Interleavable_univ x (projT2 er0))
    | Interleavable_alwaysfs A0 IA0 =>
      let: e0 := existT Interleavable A0 IA0 in
      let: er0 := restrict e' e0 in
      existT Interleavable
        (Aalwaysfs (Aimpl A' (projT1 er0)))
        (Interleavable_alwaysfs
          (Interleavable_neg
            (Interleavable_conj
              (Interleavable_neg (Interleavable_neg IA'))
              (Interleavable_neg (projT2 er0)))))
    | Interleavable_alwaysps A0 IA0 =>
      let: e0 := existT Interleavable A0 IA0 in
      let: er0 := restrict e' e0 in
      existT Interleavable
        (Aalwaysps (Aimpl A' (projT1 er0)))
        (Interleavable_alwaysps
          (Interleavable_neg
            (Interleavable_conj
              (Interleavable_neg (Interleavable_neg IA'))
              (Interleavable_neg (projT2 er0)))))
    | Interleavable_eventfs A0 IA0 =>
      let: e0 := existT Interleavable A0 IA0 in
      let: er0 := restrict e' e0 in
      existT Interleavable
        (Aeventfs (projT1 er0))
        (Interleavable_eventfs (projT2 er0))
    | Interleavable_eventps A0 IA0 =>
      let: e0 := existT Interleavable A0 IA0 in
      let: er0 := restrict e' e0 in
      existT Interleavable
        (Aeventps (projT1 er0))
        (Interleavable_eventps (projT2 er0))
    end
  end.
Next Obligation.
  rewrite /projT1 //=; apply/ltP.
  rewrite ltnS leq_max. apply/orP; by left.
Qed.
Next Obligation.
  rewrite /projT1 //=; apply/ltP.
  inversion Heq_e; inversion Heq_anonymous1. rewrite //=.
  rewrite ltnS leq_max. apply/orP; by right.
Qed.
