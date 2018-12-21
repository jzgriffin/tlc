Require Import Coq.Lists.List.
Require Import TLC.ProgramLogic.
Require Import TLC.TemporalLogic.
Require Import TLC.Term.

Import ListNotations.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Rules of sequent logic *)
Section sequent.

  Reserved Notation "X |- A"
    (at level 80, no associativity).

  Inductive sequent_logic {C} : list (term C Prop) -> term C Prop -> Prop :=

  (* Sub-logics *)
  | SequentTemporal X A :
    X |-t C, A ->
    X |- A
  | SequentProgram X A :
    X |-p C, A ->
    X |- A

  (* Axiom/assumption *)
  | SequentAxiom A :
    [A] |- A

  (* Assumption modification *)
  | SequentThin X A A' :
    X |- A' ->
    A :: X |- A'
  | SequentContraction X A A' :
    A :: A :: X |- A' ->
    A :: X |- A'
  | SequentExchange X A A' A'' :
    A :: A' :: X |- A'' ->
    A' :: A :: X |- A''
  | SequentCut X A A' :
    X |- A ->
    A :: X |- A' ->
    X |- A'

  (* Negation *)
  | SequentNotL X A A' :
    X |- A ->
    (~A)%tlc :: X |- A'
  | SequentNotR X A :
    A :: X |- ^False ->
    X |- ~A

  (* Conjunction *)
  | SequentAndL X A A' A'' :
    A :: A' :: X |- A'' ->
    (A /\ A')%tlc :: X |- A''
  | SequentAndR X A A' :
    X |- A ->
    X |- A' ->
    X |- (A /\ A')

  (* Disjunction *)
  | SequentOrL X A A' A'' :
    A :: X |- A'' ->
    A' :: X |- A'' ->
    (A \/ A')%tlc :: X |- A''
  | SequentOrRL X A A' :
    X |- A ->
    X |- (A \/ A')
  | SequentOrRR X A A' :
    X |- A' ->
    X |- (A \/ A')

  (* Implication *)
  | SequentIfL X A A' A'' :
    X |- A ->
    A' :: X |- A'' ->
    (A -> A')%tlc :: X |- A''
  | SequentIfR X A A' :
    A :: X |- A' ->
    X |- (A -> A')

  (* Universal quantification *)
  | SequentForAllL X T (x : T) A A' :
    A x :: X |- A' ->
    ForAll A :: X |- A'
  | SequentForAllR X T (x : T) A :
    X |- A x ->
    X |- ForAll A

  (* Existential quantification *)
  | SequentExistsL X T (x : T) A A' :
    A x :: X |- A' ->
    Exists A :: X |- A'
  | SequentExistsR X T (x : T) A :
    X |- A x ->
    X |- Exists A

  where "X |- A" := (sequent_logic X A).

End sequent.

Arguments sequent_logic : clear implicits.

Coercion SequentTemporal : temporal_logic >-> sequent_logic.
Coercion SequentProgram : program_logic >-> sequent_logic.

Notation "X |- C , A" := (sequent_logic C X A)
  (at level 80, no associativity).

Fixpoint rewrite_entails {C} T (t t' : term C Prop)
  (H : [] |- C, (t =>> t')) (s : term C T) : term C T.
Proof.
  destruct s eqn:eqns.
  - exact s.
  - exact s.
  - apply (Application
      (rewrite_entails _ _ t t' H t0_1)
      (rewrite_entails _ _ t t' H t0_2)).
  - destruct (term_eq_dec s t); [apply t' | ].
    apply (Not (rewrite_entails _ _ t t' H t0)).
  - destruct (term_eq_dec s t); [apply t' | ].
    apply (And
      (rewrite_entails _ _ t t' H t0_1)
      (rewrite_entails _ _ t t' H t0_2)).
  - destruct (term_eq_dec s t); [apply t' | ].
    apply (Or
      (rewrite_entails _ _ t t' H t0_1)
      (rewrite_entails _ _ t t' H t0_2)).
  - destruct (term_eq_dec s t); [apply t' | ].
    apply (If
      (rewrite_entails _ _ t t' H t0_1)
      (rewrite_entails _ _ t t' H t0_2)).
  - destruct (term_eq_dec s t); [apply t' | ].
    apply (ForAll (fun x => rewrite_entails _ _ t t' H (A x))).
  - destruct (term_eq_dec s t); [apply t' | ].
    apply (Exists (fun x => rewrite_entails _ _ t t' H (A x))).
  - destruct (term_eq_dec s t); [apply t' | ].
    apply (Always' (rewrite_entails _ _ t t' H t0)).
  - destruct (term_eq_dec s t); [apply t' | ].
    apply (AlwaysPast' (rewrite_entails _ _ t t' H t0)).
  - destruct (term_eq_dec s t); [apply t' | ].
    apply (Eventually' (rewrite_entails _ _ t t' H t0)).
  - destruct (term_eq_dec s t); [apply t' | ].
    apply (EventuallyPast' (rewrite_entails _ _ t t' H t0)).
  - destruct (term_eq_dec s t); [apply t' | ].
    apply (Next (rewrite_entails _ _ t t' H t0)).
  - destruct (term_eq_dec s t); [apply t' | ].
    apply (Self (rewrite_entails _ _ t t' H t0)).
  - destruct (term_eq_dec s t); [apply t' | ].
    apply (Equals
      (rewrite_entails _ _ t t' H t0_1)
      (rewrite_entails _ _ t t' H t0_2)).
  - exact s.
  - exact s.
  - exact s.
Defined.

Lemma rewrite_entails_correct {C} (t t' : term C Prop)
  (H : [] |- C, (t =>> t')) (s : term C Prop) :
  [] |- C, rewrite_entails H s <-> [] |- C, s.
Proof.
Admitted. (* TODO *)

Ltac rewrite_entails H :=
  apply (rewrite_entails_correct H); simpl.

Definition cong_left {C} (t t' : term C Prop)
  (H : [] |- C, (t <=> t')) : [] |- C, (t =>> t') :=
  let H' : [ ] |- C, (t =>> t') :=
  SequentCut H
    (SequentAndL
      (SequentExchange
        (SequentThin (t' =>> t) (SequentAxiom (t =>> t'))))) in H'.

Lemma rewrite_cong_left_correct {C} (t t' : term C Prop)
  (H : [] |- C, (t <=> t')) (s : term C Prop) :
  [] |- C, rewrite_entails (cong_left H) s <-> [] |- C, s.
Proof.
  apply rewrite_entails_correct.
Qed.

Ltac rewrite_cong_left H :=
  apply (rewrite_cong_left_correct H); simpl.

Definition cong_right {C} (t t' : term C Prop)
  (H : [] |- C, (t <=> t')) : [] |- C, (t' =>> t) :=
  let H' : [ ] |- C, (t' =>> t) :=
  SequentCut H
    (SequentAndL
      (SequentThin (t =>> t') (SequentAxiom (t' =>> t)))) in H'.

Lemma rewrite_cong_right_correct {C} (t t' : term C Prop)
  (H : [] |- C, (t <=> t')) (s : term C Prop) :
  [] |- C, rewrite_entails (cong_right H) s <-> [] |- C, s.
Proof.
  apply rewrite_entails_correct.
Qed.

Ltac rewrite_cong_right H :=
  apply (rewrite_cong_right_correct H); simpl.
