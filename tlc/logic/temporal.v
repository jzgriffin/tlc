(* TLC in Coq
 *
 * Module: tlc.logic.temporal
 * Purpose: Contains derived rules and lemmas regarding temporal logic.
 *)

Require Import mathcomp.ssreflect.eqtype.
Require Import mathcomp.ssreflect.seq.
Require Import mathcomp.ssreflect.ssrbool.
Require Import mathcomp.ssreflect.ssreflect.
Require Import tlc.component.component.
Require Import tlc.logic.context.
Require Import tlc.logic.derives.
Require Import tlc.logic.sequent.
Require Import tlc.semantics.all_semantics.
Require Import tlc.syntax.all_syntax.
Require Import tlc.utility.result.
Require Import tlc.utility.seq.
 
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Temporal logic tactics *)
Ltac dtgenp_keep :=
  match goal with
  | |- Context _ (?H :: _) ||- _, _ =>
    eapply DSCut; first by apply DTGeneralization with (A := H);
      first by repeat constructor
  end.
Ltac dtgenp := dtgenp_keep; dswap; dclear.
Ltac dtgen :=
  apply DTGeneralization; first by repeat constructor.

(* Particularization *)
Lemma DTPar C Delta Gamma A :
  Context Delta Gamma ||- C, {-A always A -} ->
  Context Delta Gamma ||- C, {-A A -}.
Proof.
  move=> H.
  duse DT1; instantiate (1 := A).
  by difp; first by exact: H.
Qed.

(* Entailment modus ponens *)
Lemma DTMP C Delta Gamma H A :
  Context Delta Gamma ||- C, {-A H =>> A -} ->
  Context Delta Gamma ||- C, {-A always H -} ->
  Context Delta Gamma ||- C, {-A always A -}.
Proof.
  move=> HHA HH.
  duse DT4; instantiate (1 := A); instantiate (2 := H).
  eapply DSCut; first by apply DTPar; dhead.
  difp; first by dclear.
  by difp; first by dclear.
Qed.

(* Entailment transitivity *)
Lemma DTTrans C Z A1 A2 A3 :
  Z ||- C, {-A A1 =>> A2 -} ->
  Z ||- C, {-A A2 =>> A3 -} ->
  Z ||- C, {-A A1 =>> A3 -}.
Proof.
Admitted.

Ltac dttrans :=
  match goal with
  | |- Context _ (AEntails _ ?A :: _) ||- _, AEntails _ _ =>
    eapply DTTrans with (A2 := A); [try by [] |]
  end.
Ltac dttransp_keep :=
  match goal with
  | |- Context _ ({-A ?H2 =>> ?H3 -} :: {-A ?H1 =>> ?H2 -} :: _) ||- _, _ =>
    eapply DSCut;
      first by eapply DTTrans with (A1 := H1) (A2 := H2) (A3 := H3);
      dassumption
  end.
(* Apply transitivity on the two head premises and remove them *)
Ltac dttransp := dttransp_keep; dswap; dclear; dswap; dclear.

(* State substituvity *)
Axiom DSSubst :
  forall C Z A1 A2 u A,
  non_temporal_assertion A ->
  Z ||- C, {-A A1 <-> A2 -} ->
  Z ||- C, {-A
    (replace_assertion u A1 A) <-> (replace_assertion u A2 A)
  -}.

(* Temporal substitutivity *)
Axiom DTSubst :
  forall C Z A1 A2 u A,
  Z ||- C, {-A A1 <=> A2 -} ->
  Z ||- C, {-A
    (replace_assertion u A1 A) <=> (replace_assertion u A2 A)
  -}.

(* Positive polarity *)
Axiom DTSubstPos :
  forall C Z A1 A2 u A,
  all_assertion_occ_pos u A ->
  Z ||- C, {-A A1 =>> A2 -} ->
  Z ||- C, {-A
    ((replace_assertion u A1 A) =>> (replace_assertion u A2 A))
  -}.
Ltac dtsubstposp :=
  match goal with
  | |- Context _ (AEntails ?A1_ ?A2_ :: ?A_ :: _) ||- _, _ =>
    eapply DSCut;
    [eapply DTSubstPos with (A1 := A1_) (A2 := A2_) (u := A1_) (A := A_);
      [try by rewrite /all_assertion_occ_pos /all_assertion_occ_rec
        /= ?eq_refl ?if_same | try by [] ] |
    simpl; dclean; rewrite ?eq_refl;
    dsplitp; dswap; dclear; difp; [by dclear | do 2 (dswap; dclear)] ]
  end.

(* Negative polarity *)
Axiom DTSubstNeg :
  forall C Z A1 A2 u A,
  all_assertion_occ_neg u A ->
  Z ||- C, {-A A1 =>> A2 -} ->
  Z ||- C, {-A
    ((replace_assertion u A2 A) =>> (replace_assertion u A1 A))
  -}.

(* Reflexivity of equality *)
Axiom DTReflE :
  forall C Z t,
  Z ||- C, {-A always (t = t) -}.

(* Replacement of equals by equals *)
Axiom DTReplE :
  forall C Z (x : variable) t1 t2 A,
  x \in assertion_vars A ->
  non_temporal_assertion A ->
  term_replace_admissible x t1 ->
  term_replace_admissible x t2 ->
  Z ||- C, {-A
    (t1 = t2) =>>
    (replace_assertion_var x t1 A <-> replace_assertion_var x t2 A)
  -}.

(* Substitutivity of equality *)
Lemma DTSubstE :
  forall C Z (x : variable) t1 t2 A,
  x \in assertion_vars A ->
  term_replace_admissible x t1 ->
  term_replace_admissible x t2 ->
  Z ||- C, {-A
    always (t1 = t2) ->
    (replace_assertion_var x t1 A <=> replace_assertion_var x t2 A)
  -}.
Proof.
Admitted.

(* Conditional substitutivity of equality *)
Lemma DTIfSubstE :
  forall C Z (x : variable) t1 t2 H A,
  x \in assertion_vars A ->
  term_replace_admissible x t1 ->
  term_replace_admissible x t2 ->
  Z ||- C, {-A
    (t1 = t2 /\ H =>> replace_assertion_var x t1 A) <=>
    (t1 = t2 /\ H =>> replace_assertion_var x t2 A)
  -}.
Proof.
Admitted.

Ltac dtifsubste_pl :=
  match goal with
  | |- Context _ ({-A ?H_ =>> ?A_ -} :: _) ||- _,
    {-A TVariable ?x1 = TVariable ?x2 /\ ?H_ =>> _ -} =>
    eapply DSCut; [eapply DTIfSubstE with
      (x := x1) (t1 := x1) (t2 := x2) (H := H_) (A := A_) |];
      [by repeat auto_mem | by [] | by [] |]
  end;
  rewrite /replace_assertion_var /=
    ?replace_rigid_term_flexible_var
    ?replace_gc_term_rigid_var;
    (try by exact: computable_term_rigid);
    (try by exact: computable_term_closed);
    last (dclean; dsplitp; dswap; dclear; dsplitp; dswap; dclear;
      difp; last by []).

(* Quantifier duality *)
Axiom DTQDual :
  forall C Z A,
  Z ||- C, {-A
    (~exists: A) <=> (forall: ~A)
  -}.

(* Quantifier instantiation *)
Axiom DTForAllIns :
  forall C Delta Gamma t A A',
  term_closed_in [::] Delta t ->
  open_assertion [:: t] A = Success A' ->
  Context Delta Gamma ||- C, {-A
    (forall: A) =>> A'
  -}.

(* These rules and lemmas are taken directly from the appendix *)

Lemma DTL76 C Z A1 A2 :
  Z ||- C, {-A A1 =>> A2 -} ->
  Z ||- C, {-A always A1 -} ->
  Z ||- C, {-A always A2 -}.
Proof.
Admitted.

Definition DTL77 := DTTrans.

Lemma DTL78_1 C Z A1 A2 :
  Z ||- C, {-A A1 =>> A2 -} ->
  Z ||- C, {-A next A1 =>> next A2 -}.
Proof.
Admitted.

Lemma DTL78_2 C Z A1 A2 :
  Z ||- C, {-A A1 <=> A2 -} ->
  Z ||- C, {-A next A1 <=> next A2 -}.
Proof.
Admitted.

Lemma DTL79 C Z A :
  Z ||- C, {-A A =>> next A -} ->
  Z ||- C, {-A A =>> always A -}.
Proof.
Admitted.

Lemma DTL80 C Z A :
  Z ||- C, {-A always A =>> A -}.
Proof.
  (* Used in PLC *)
Admitted.

Lemma DTL81 C Z A1 A2 :
  Z ||- C, {-A always (A1 /\ A2) <=> always A1 /\ always A2 -}.
Proof.
Admitted.

Lemma DTL83_1 C Z A :
  Z ||- C, {-A eventuallyp A <=> eventuallyp eventuallyp A -}.
Proof.
  (* Used in SLC & PLC *)
Admitted.

Lemma DTL83_2 C Z A :
  Z ||- C, {-A eventuallyp^ eventuallyp^ A =>> eventuallyp^ A -}.
Proof.
Admitted.

Lemma DTL83_3 C Z A :
  Z ||- C, {-A eventuallyp eventuallyp^ A =>> eventuallyp^ A -}.
Proof.
Admitted.

Lemma DTL83_4 C Z A :
  Z ||- C, {-A eventuallyp^ eventuallyp A =>> eventuallyp^ A -}.
Proof.
Admitted.

Lemma DTL84 C Z A :
  Z ||- C, {-A eventually A <=> eventually eventually A -}.
Proof.
  (* Used in PLC *)
Admitted.

Lemma DTL85 C Z A1 A2 A3 :
  Z ||- C, {-A A1 =>> eventuallyp A2 -} ->
  Z ||- C, {-A A2 =>> eventuallyp A3 -} ->
  Z ||- C, {-A A1 =>> eventuallyp A3 -}.
Proof.
  (* Used in SLC & PLC *)
Admitted.

Lemma DTL86 C Z A1 A2 A3 :
  Z ||- C, {-A A1 =>> eventually A2 -} ->
  Z ||- C, {-A A2 =>> eventually A3 -} ->
  Z ||- C, {-A A1 =>> eventually A3 -}.
Proof.
Admitted.

Lemma DTL87 C Z A :
  Z ||- C, {-A A =>> eventuallyp A -}.
Proof.
  (* Used in PLC *)
Admitted.

Lemma DTL90 C Z A :
  Z ||- C, {-A (self ~A) <=> ~self A -}.
Proof.
Admitted.

Lemma DTL91 C Z A :
  Z ||- C, {-A A -> previous^ next A -}.
Proof.
Admitted.

Lemma DTL94 C Z A1 A2 :
  Z ||- C, {-A (A1 =>> A2) /\ A1 -> A2 -}.
Proof.
Admitted.

Lemma DTL96_1 C Z A1 A2 A3 :
  Z ||- C, {-A
    (A1 =>> eventually A2) /\ (A2 =>> A3) ->
    A1 =>> eventually A3
  -}.
Proof.
Admitted.

Lemma DTL96_1_b C Z A1 A2 A3 :
  Z ||- C, {-A
     (A1 =>> A2) /\ (A2 =>> eventually A3) ->
     A1 =>> eventually A3
  -}.
Proof.
Admitted.

Lemma DTL96_2 C Z A1 A2 A3 :
  Z ||- C, {-A
    (A1 =>> eventuallyp A2) /\ (A2 =>> A3) ->
    A1 =>> eventuallyp A3
  -}.
Proof.
  (* Used in PLC *)
Admitted.

Lemma DTL96_3 C Z A1 A2 A3 :
  Z ||- C, {-A
    (A1 =>> eventuallyp^ A2) /\ (A2 =>> A3) ->
    A1 =>> eventuallyp^ A3
  -}.
Proof.
Admitted.

Lemma DTL97 C Z A1 A2 A3 :
  Z ||- C, {-A (A1 =>> always A2) /\ (A2 =>> A3) -> A1 =>> always A3 -}.
Proof.
  (* Used in PLC *)
Admitted.

Lemma DTL98_1 C Z A :
  Z ||- C, {-A eventuallyp always A =>> A -}.
Proof.
  (* Used in PLC *)
Admitted.

Lemma DTL98_2 C Z A :
  Z ||- C, {-A eventuallyp always^ A =>> A -}.
Proof.
Admitted.

Lemma DTL98_3 C Z A :
  Z ||- C, {-A eventuallyp^ always A =>> A -}.
Proof.
Admitted.

Lemma DTL100 C Z A :
  Z ||- C, {-A A -> alwaysp^ (A =>> self A) =>> A -}.
Proof.
Admitted.

Lemma DTL102_1 C Z A1 A2 :
  Z ||- C, {-A
    eventually A1 /\ eventually A2 =>>
      eventually (A1 /\ eventually A2) \/
      eventually (A2 /\ eventually A1)
  -}.
Proof.
Admitted.

Lemma DTL102_2 C Z A1 A2 :
  Z ||- C, {-A
    eventuallyp A1 /\ eventuallyp A2 =>>
      eventuallyp (A1 /\ eventuallyp A2) \/
      eventuallyp (A2 /\ eventuallyp A1)
  -}.
Proof.
  (* Used in PLC *)
Admitted.

Lemma DTL102_3 C Z A1 A2 :
  Z ||- C, {-A
    eventuallyp A1 /\ eventually A2 =>>
    eventuallyp (A1 /\ eventually A2)
  -}.
Proof.
Admitted.

Lemma DTL103_1 C Z A :
  Z ||- C, {-A (eventually A /\ always^ ~A) =>> A -}.
Proof.
Admitted.

Lemma DTL103_2 C Z A :
  Z ||- C, {-A (eventuallyp A /\ alwaysp^ ~A) =>> A -}.
Proof.
  (* Used in PLC *)
Admitted.

Lemma DTL104 C Z A :
  Z ||- C, {-A eventuallyp A =>> always eventuallyp A -}.
Proof.
  (* Used in PLC *)
Admitted.

Lemma DTL105_1 C Z A :
  Z ||- C, {-A (A =>> always^ ~A) -> A =>> alwaysp^ ~A -}.
Proof.
  (* Used in PLC *)
Admitted.

Lemma DTL105_2 C Z A :
  Z ||- C, {-A (A =>> alwaysp^ ~A) -> A =>> always^ ~A -}.
Proof.
Admitted.

Lemma DTL106 C Z A1 A2 :
  Z ||- C, {-A (A1 =>> eventuallyp (A1 =>> A2)) -> A1 =>> A2 -}.
Proof.
Admitted.

Lemma DTL107 C Z A :
  Z ||- C, {-A (alwaysp^ A =>> A) -> always A -}.
Proof.
Admitted.

Lemma DTL108 C Z A1 A2 :
  Z ||- C, {-A
    (alwaysp^ A1 /\ alwaysp^ A2 =>> A1 /\ A2) -> always (A1 /\ A2)
  -}.
Proof.
Admitted.

Lemma DTL109_1 C Z A :
  Z ||- C, {-A
    eventuallyp eventually A <=> eventually A \/ eventuallyp A
  -}.
Proof.
Admitted.

Lemma DTL109_2 C Z A :
  Z ||- C, {-A
    eventuallyp^ eventually A =>> eventually A \/ eventuallyp A
  -}.
Proof.
Admitted.

Lemma DTL109_3 C Z A :
  Z ||- C, {-A
    eventually eventuallyp A =>> eventually A \/ eventuallyp A
  -}.
Proof.
Admitted.

Lemma DTL109_3_a C Z A :
  Z ||- C, {-A
    eventually eventuallyp A =>> eventually^ A \/ A \/ eventuallyp^ A
  -}.
Proof.
  (* Used in PLC *)
Admitted.

Lemma DTL109_4 C Z A :
  Z ||- C, {-A
    eventually eventuallyp^ A =>> eventually A \/ eventuallyp A
  -}.
Proof.
Admitted.

Lemma DTL109_5 C Z A :
  Z ||- C, {-A
    eventuallyp^ eventually^ A =>> eventually A \/ eventuallyp A
  -}.
Proof.
Admitted.

Lemma DTL111 C Z A :
  Z ||- C, {-A eventuallyp A <=> self eventuallyp^ A -}.
Proof.
Admitted.

Lemma DTL112 C Z A1 A2 :
  Z ||- C, {-A
    eventually A1 /\ always A2 =>> eventually (A1 /\ always A2)
  -}.
Proof.
Admitted.

Lemma DTL114 C Z A :
  Z ||- C, {-A ~eventuallyp^ A <=> alwaysp^ ~A -}.
Proof.
  (* Used in PLC *)
Admitted.

Lemma DTL114_1 C Z A :
  Z ||- C, {-A ~eventually^ A <=> always^ ~A -}.
Proof.
  (* Used in PLC *)
Admitted.

Lemma DTL115 C Z A :
  Z ||- C, {-A alwaysp^ A <=> alwaysp previous^ A -}.
Proof.
Admitted.

Lemma DTL116 C Z A1 A2 :
  Z ||- C, {-A
    A1 /\ eventuallyp^ A2 =>>
    eventuallyp^ (A2 /\ eventually A1)
  -}.
Proof.
Admitted.

Lemma DTL117 C Z A :
  Z ||- C, {-A
    alwaysp A /\ always A =>>
    alwaysp alwaysp^ A /\ always alwaysp^ A
  -}.
Proof.
Admitted.

Lemma DTL118 C Z A :
  Z ||- C, {-A eventuallyp^ self A <=> eventuallyp A -}.
Proof.
Admitted.

(* These rules and lemmas are new and do not yet appear in the appendix *)

Lemma DTL119 C Z A :
  Z ||- C, {-A always^ always A <=> always^ A -}.
Proof.
  (* Used in SLC *)
Admitted.

Lemma DTL120_1 C Z A :
  Z ||- C, {-A eventually A <=> eventually eventually A -}.
Proof.
Admitted.

Lemma DTL120_2 C Z A :
  Z ||- C, {-A eventually^ eventually^ A =>> eventually^ A -}.
Proof.
Admitted.

Lemma DTL120_3 C Z A :
  Z ||- C, {-A eventually eventually^ A =>> eventually^ A -}.
Proof.
  (* Used in SLC *)
Admitted.

Lemma DTL120_4 C Z A :
  Z ||- C, {-A eventually^ eventually A =>> eventually^ A -}.
Proof.
Admitted.

Lemma DTL121 C Delta Gamma A :
  Context Delta Gamma ||- C, {-A eventually^ A -> eventually A -}.
Proof.
  by dif; dright.
Qed.

Lemma DTL122 C Z A :
  Z ||- C, {-A always^ eventually A -> always eventually A -}.
Proof.
  (* Used in SLC *)
Admitted.

Lemma DTL123 C Delta Gamma A :
  Context Delta Gamma ||- C, {-A eventuallyp^ A -> eventuallyp A -}.
Proof.
  by dif; dright.
Qed.

Lemma DTL124 C Z Ap Ac :
  Z ||- C, {-A (Ac /\ always^ (Ap -> Ac)) =>> (Ap =>> Ac) -}.
Proof.
  (* Used in PLC *)
Admitted.

Lemma DTL125 C Z Ap Ac :
  Z ||- C, {-A (Ap -> (Ap =>> Ac)) =>> (Ap =>> Ac) -}.
Proof.
  (* Used in PLC *)
Admitted.

Lemma DTL126 C Z A B :
  Z ||- C, {-A
    eventuallyp (eventuallyp A /\ eventually B) ->
    eventuallyp (A /\ eventually B)
  -}.
Proof.
  (* Provable by DTL102_3 and DTL83_1 *)
Admitted.

(* Distribution properties, FD1 and FD2 *)
Lemma DTL127_1 C Z A B :
  Z ||- C, {-A eventually (A \/ B) <=> (eventually A) \/ (eventually B) -}.
Proof.
  (* Used in PLC *)
Admitted.

Lemma DTL127_2 C Z A :
  Z ||- C, {-A eventually (exists: A) <=> (exists: eventually A) -}.
Proof.
  (* Used in PLC *)
Admitted.

Lemma DTL127_3 C Z A :
  Z ||- C, {-A eventuallyp (exists: A) <=> (exists: eventuallyp A) -}.
Proof.
  (* Used in PLC *)
Admitted.

Lemma DTL127_4 C Z A B :
  Z ||- C, {-A eventually (A /\ B) =>> (eventually A) /\ (eventually B) -}.
Proof.
Admitted.

Lemma DTL127_5 C Z A B :
  Z ||- C, {-A eventuallyp (A /\ B) =>> (eventuallyp A) /\ (eventuallyp B) -}.
Proof.
  (* Used in PLC *)
Admitted.

Lemma DTL128_1 C Z A B :
  Z ||- C, {-A always (A /\ B) <=> (always A) /\ (always B) -}.
Proof.
  (* Used in PLC *)
Admitted.

Lemma DTL128_2 C Z A :
  Z ||- C, {-A always (forall: A) <=> (forall: always A) -}.
Proof.
Admitted.

Lemma DTL128_3 C Z A B :
  Z ||- C, {-A always^ (A /\ B) <=> (always^ A) /\ (always^ B) -}.
Proof.
  (* Used in PLC *)
Admitted.

Lemma DTL129 C Z A :
  Z ||- C, {-A A -> self A -}.
Proof.
  (* Used in PLC *)
Admitted.

(* Distribution properties of self *)
Lemma DTL130 C Z A B :
  Z ||- C, {-A self (A /\ B) <-> self A /\ self B -}.
Proof.
  (* Used in PLC *)
Admitted.

(* Self distributes over if *)
Lemma DTL131 C Z A B :
  Z ||- C, {-A self (A -> B) -> (self A -> self B) -}.
Proof.
  (* Used in PLC *)
Admitted.

Lemma DTL132 C Z A1 B1 A2 B2 :
  Z ||- C, {-A
    ((A1 =>> B1) /\ (A2 =>> B2)) ->
    ((A1 /\ A2) =>> (B1 /\ B2))
  -}.
Proof.
  (* Used in PLC *)
Admitted.

Lemma DTL133 C Z P :
  rigid_predicate P ->
  Z ||- C, {-A eventuallyp P -> P -}.
Proof.
  (* Used in PLC *)
Admitted.

Lemma DTEntailsTautology C Z A :
  Z ||- C, {-A
    A =>> A
  -}.
Proof.
Admitted.

Hint Resolve DTEntailsTautology : core.

Lemma DTEntailsAndDropRight C Z A1 A2 :
  Z ||- C, {-A
    A1 /\ A2 =>> A1
  -}.
Proof.
Admitted.

Hint Resolve DTEntailsAndDropRight : core.

Ltac dtentails_l := eapply DTTrans; first by exact: DTEntailsAndDropRight.

Lemma DTEntailsAndDropLeft C Z A1 A2 :
  Z ||- C, {-A
    A1 /\ A2 =>> A2
  -}.
Proof.
Admitted.

Hint Resolve DTEntailsAndDropLeft : core.

Ltac dtentails_r := eapply DTTrans; first by exact: DTEntailsAndDropLeft.

Lemma DTEntailsSplitAnd C Z H1 H2 A :
  Z ||- C, {-A H1 =>> H2 =>> A -} ->
  Z ||- C, {-A H1 /\ H2 =>> A -}.
Proof.
Admitted.

Lemma DTEntailsMergeAnd C Z H A1 A2 :
  Z ||- C, {-A
    (H =>> A1) /\ (H =>> A2) ->
    (H =>> A1 /\ A2)
  -}.
Proof.
Admitted.

Lemma DTEntailsAndAssocP C Z H1 H2 H3 A :
  Z ||- C, {-A (H1 /\ H2) /\ H3 =>> A -} <->
  Z ||- C, {-A H1 /\ (H2 /\ H3) =>> A -}.
Proof.
Admitted.

Lemma DTEntailsAndAssocC C Z H A1 A2 A3 :
  Z ||- C, {-A H =>> (A1 /\ A2) /\ A3 -} <->
  Z ||- C, {-A H =>> A1 /\ (A2 /\ A3) -}.
Proof.
Admitted.

Lemma DTEntailsAndSplitC C Z H A1 A2 :
  Z ||- C, {-A H =>> A1 /\ A2 -} <->
  Z ||- C, {-A H =>> A1 -} /\ Z ||- C, {-A H =>> A2 -}.
Proof.
Admitted.
