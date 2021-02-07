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
  forall C Z R R1 R2 uss R1' R2' A,
  non_temporal_assertion A ->
  split_implication R = Some (AIff, R1, R2) ->
  unify_sub_assertion R1 A = Some uss ->
  open_assertion_multi uss R1 = Success R1' ->
  open_assertion_multi uss R2 = Success R2' ->
  Z ||- C, R ->
  Z ||- C, {-A
    replace_assertion R1' R2' A <-> replace_assertion R2' R1' A
  -}.

(* Temporal substitutivity *)
Axiom DTSubstL :
  forall C Z R R1 R2 uss R1' R2' A,
  split_implication R = Some (ACongruent, R1, R2) ->
  unify_sub_assertion R2 A = Some uss ->
  open_assertion_multi uss R1 = Success R1' ->
  open_assertion_multi uss R2 = Success R2' ->
  Z ||- C, R ->
  Z ||- C, {-A
    A <=> replace_assertion R2' R1' A
  -}.
Axiom DTSubstR :
  forall C Z R R1 R2 uss R1' R2' A,
  split_implication R = Some (ACongruent, R1, R2) ->
  unify_sub_assertion R1 A = Some uss ->
  open_assertion_multi uss R1 = Success R1' ->
  open_assertion_multi uss R2 = Success R2' ->
  Z ||- C, R ->
  Z ||- C, {-A
    A <=> replace_assertion R1' R2' A
  -}.

(* Positive polarity *)
Axiom DTSubstPos :
  forall C Z R RH RA uss RH' RA' A,
  split_implication R = Some (AEntails, RH, RA) ->
  unify_sub_assertion RH A = Some uss ->
  open_assertion_multi uss RH = Success RH' ->
  open_assertion_multi uss RA = Success RA' ->
  all_assertion_occ_pos RH' A ->
  Z ||- C, R ->
  Z ||- C, {-A
    A =>> replace_assertion RH' RA' A
  -}.
Ltac dtsubstposp_keep :=
  match goal with
  | |- Context _ (?R_ :: ?A_ :: _) ||- _, _ =>
    eapply DSCut; [eapply DTSubstPos with (R := R_) (A := A_);
      [by dsplitimpl | by dunify | by [] | by [] |
        by rewrite /all_assertion_occ_pos /=; repeat dautoeq | by [] ] |
      dclean; dsplitp; dswap; dclear; difp; first by dassumption]
  end.
Ltac dtsubstposp := dtsubstposp_keep; do 2 (dswap; dclear); repeat dautoeq.

(* Negative polarity *)
Axiom DTSubstNegP :
  forall C Z R RH RA uss RH' RA' A,
  split_implication R = Some (AEntails, RH, RA) ->
  unify_sub_assertion RA A = Some uss ->
  open_assertion_multi uss RH = Success RH' ->
  open_assertion_multi uss RA = Success RA' ->
  all_assertion_occ_neg RA' A ->
  Z ||- C, R ->
  Z ||- C, {-A
    A =>> replace_assertion RA' RH' A
  -}.
Ltac dtsubstnegp_keep :=
  match goal with
  | |- Context _ (?R_ :: ?A_ :: _) ||- _, _ =>
    eapply DSCut; [eapply DTSubstNegP with (R := R_) (A := A_);
      [by dsplitimpl | by dunify | by [] | by [] |
        by rewrite /all_assertion_occ_neg /=; repeat dautoeq | by [] ] |
      dclean; dsplitp; dswap; dclear; difp; first by dassumption]
  end.
Ltac dtsubstnegp := dtsubstnegp_keep; do 2 (dswap; dclear); repeat dautoeq.

Axiom DTSubstNeg :
  forall C Z R RH RA uss RH' RA' A,
  split_implication R = Some (AEntails, RH, RA) ->
  unify_sub_assertion RH A = Some uss ->
  open_assertion_multi uss RH = Success RH' ->
  open_assertion_multi uss RA = Success RA' ->
  all_assertion_occ_neg RA' A ->
  Z ||- C, R ->
  Z ||- C, {-A
    replace_assertion RH' RA' A =>> A
  -}.
Ltac dtsubstneg_keep :=
  match goal with
  | |- Context _ (?R_ :: _) ||- _, ?A_ =>
    eapply DSCut; [eapply DTSubstNeg with (R := R_) (A := A_);
      [by dsplitimpl | by dunify | by [] | by [] |
        by rewrite /all_assertion_occ_neg /=; repeat dautoeq | by [] ] |
      dclean; dsplitp; dswap; dclear; difp; last by [] ]
  end; repeat dautoeq.
Ltac dtsubstneg := dtsubstneg_keep; dclear.

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

(* Direct replacement of equals by equals for terms *)
Lemma DTReplE' :
  forall C Z t1 t2 A,
  non_temporal_assertion A ->
  (~ term_rigid t1) \/ (term_rigid t1 /\ term_rigid t2) ->
  Z ||- C, {-A
    (t1 = t2 =>> A) <=>
    (t1 = t2 =>> replace_assertion_term t1 t2 A)
  -}.
Proof.
Admitted.

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

(* Direct substitutivity of equality for terms *)
Lemma DTSubstE' :
  forall C Z t1 t2 A,
  (~ term_rigid t1) \/ (term_rigid t1 /\ term_rigid t2) ->
  Z ||- C, {-A
    always (t1 = t2) ->
    (A <=> replace_assertion_term t1 t2 A)
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

(* Conditional substitutivity of equality in bulk *)
Lemma DTIfSubstE' :
  forall C Z H A,
  let ps := extract_equalities (split_conjunction H) in
  all (fun '(t1, t2) => (~~term_rigid t1) || (term_rigid t1 && term_rigid t2)) ps ->
  let A' := foldr (fun '(t1, t2) A => replace_assertion_term t1 t2 A) A ps in
  Z ||- C, {-A (H =>> A) <=> (H =>> A') -}.
Proof.
Admitted.

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

(* Apply constructor injection within the head premise *)
Ltac dtinjectionp := repeat (dinjection; dtgenp; dclean; dtsubstposp).

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

Ltac dteventuallyidemp :=
  match goal with
  | |- context[ {-A eventually eventually ?A_ -} ] =>
    eapply DSCut; first (by repeat dclear; apply DTL84 with (A := A_))
  end.

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
  Z ||- C, {-A (A1 =>> always A2) /\ (A2 =>> A3) =>> A1 =>> always A3 -}.
Proof.
  (* Used in PLC *)
Admitted.
Ltac dtl97 :=
  match goal with
  | |- context[ {-A (?A1_ =>> always ?A2_) /\ (?A2_ =>> ?A3_) -} ] =>
    eapply DSCut; first (by repeat dclear; apply DTL97 with
      (A1 := A1_) (A2 := A2_) (A3 := A3_))
  end.

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

Lemma DTL103_1 C Delta A1 A2 :
  Context Delta [::] ||- C, {-A
    (eventually (A1 /\ A2) /\ always^ ~A1) =>>
    A1 /\ A2
  -}.
Proof.
Admitted.

Lemma DTL103_2 C Delta A1 A2 :
  Context Delta [::] ||- C, {-A
    (eventuallyp (A1 /\ A2) /\ alwaysp^ ~A1) =>>
    A1 /\ A2
  -}.
Proof.
Admitted.

Lemma DTL104 C Z A :
  Z ||- C, {-A eventuallyp A =>> always eventuallyp A -}.
Proof.
  (* Used in PLC *)
Admitted.

Lemma DTL105_1 C Z H A :
  Z ||- C, {-A (H =>> always^ ~A) =>> H =>> alwaysp^ ~A -}.
Proof.
  (* Used in PLC *)
Admitted.
Ltac dtl105_1 :=
  match goal with
  | |- context[ {-A ?H_ =>> always^ ~?A_ -} ] =>
    eapply DSCut; first (by repeat dclear; apply DTL105_1 with
      (H := H_) (A := A_))
  end.

Lemma DTL105_2 C Z H A :
  Z ||- C, {-A (H =>> alwaysp^ ~A) -> H =>> always^ ~A -}.
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

Lemma DTL121 C Z A :
  Z ||- C, {-A eventually^ A =>> eventually A -}.
Proof.
  (* Used in SLC *)
Admitted.

Lemma DTL122 C Z A :
  Z ||- C, {-A always^ eventually A =>> always eventually A -}.
Proof.
  (* Used in SLC *)
Admitted.

Lemma DTL123 C Z A :
  Z ||- C, {-A eventuallyp^ A =>> eventuallyp A -}.
Proof.
Admitted.

Lemma DTL124 C Z Ap Ac :
  Z ||- C, {-A (Ac /\ always^ (Ap -> Ac)) =>> (Ap =>> Ac) -}.
Proof.
  (* Used in PLC *)
Admitted.
Ltac dtl124 :=
  match goal with
  | |- context[ {-A ?Ac_ /\ always^ (?Ap_ -> ?Ac_) -} ] =>
    eapply DSCut; first (by repeat dclear; apply DTL124 with
      (Ap := Ap_) (Ac := Ac_))
  end.

Lemma DTL125 C Z Ap Ac :
  Z ||- C, {-A (Ap -> (Ap =>> Ac)) =>> (Ap =>> Ac) -}.
Proof.
  (* Used in PLC *)
Admitted.
Ltac dtl125 :=
  match goal with
  | |- context[ {-A ?Ap_ -> (?Ap_ =>> ?Ac_) -} ] =>
    eapply DSCut; first (by repeat dclear; apply DTL125 with
      (Ap := Ap_) (Ac := Ac_))
  end.

Lemma DTL126 C Delta A1 A2 :
  Context Delta [::] ||- C, {-A
    eventuallyp (eventuallyp A1 /\ eventually A2) =>>
    eventuallyp (A1 /\ eventually A2)
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

Ltac dteventuallyorcomm :=
  match goal with
  | |- context[ {-A eventually (?A1_ \/ ?A2_) -} ] =>
    eapply DSCut; first (by repeat dclear; apply DTL127_1 with
      (A := A1_) (B := A2_))
  end.

Lemma DTL127_2 C Z A :
  Z ||- C, {-A eventually (exists: A) <=> (exists: eventually A) -}.
Proof.
  (* Used in PLC *)
Admitted.

Ltac dteventuallyexistscomm :=
  match goal with
  | |- context[ {-A eventually (exists: ?A_) -} ] =>
    eapply DSCut; first (by repeat dclear; apply DTL127_2 with
      (A := A_))
  end.

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
Lemma DTSelfDistribAnd C Z A B :
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

Lemma DTL133 C Z P :
  rigid_predicate P ->
  Z ||- C, {-A eventuallyp P -> P -}.
Proof.
  (* Used in PLC *)
Admitted.

Definition DTEventually' := DTL121.
Ltac dteventually'p :=
  match goal with
  | |- context[ {-A eventually^ ?A_ -} ] =>
    eapply DSCut; first (by repeat dclear; eapply DTEventually' with
      (A := A_));
    dtsubstposp
  end.

Definition DTEventuallyP' := DTL123.
Ltac dteventuallyp'p :=
  match goal with
  | |- context[ {-A eventuallyp^ ?A_ -} ] =>
    eapply DSCut; first (by repeat dclear; eapply DTEventuallyP' with
      (A := A_));
    dtsubstposp
  end.

Lemma DTAndEntails C Delta H A :
  Context Delta [::] ||- C, {-A
    H /\ (H =>> A) =>>
    always A
  -}.
Proof.
Admitted.

Lemma DTUnionEntails C Delta H1 A1 H2 A2 :
  Context Delta [::] ||- C, {-A
    ((H1 =>> A1) /\ (H2 =>> A2)) =>>
    H1 /\ H2 =>> A1 /\ A2
  -}.
Proof.
  (* Used in PLC *)
Admitted.
Ltac dtunionentails :=
  match goal with
  | |- context[ {-A (?H1_ =>> ?A1_) /\ (?H2_ =>> ?A2_) -} ] =>
    eapply DSCut; first (by repeat dclear; apply DTUnionEntails with
      (H1 := H1_) (A1 := A1_) (H2 := H2_) (A2 := A2_))
  end.

Lemma DTAndElimSelf C Delta A :
  Context Delta [::] ||- C, {-A
    A /\ A <=> A
  -}.
Proof.
Admitted.
Ltac dtandelimself :=
  match goal with
  | |- context[ {-A ?A_ /\ ?A_ -} ] =>
    eapply DSCut; first (by repeat dclear; apply DTAndElimSelf with (A := A_))
  end.

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

Lemma DTEntailsAndSplitP C Delta Gamma H A1 A2 A :
  Context Delta ({-A H =>> A1 /\ A2 -} :: Gamma) ||- C, A <->
  Context Delta ({-A H =>> A1 -} :: {-A H =>> A2 -} :: Gamma) ||- C, A.
Proof.
Admitted.

Lemma DTEntailsAndSplitC C Z H A1 A2 :
  Z ||- C, {-A H =>> A1 /\ A2 -} <->
  Z ||- C, {-A H =>> A1 -} /\ Z ||- C, {-A H =>> A2 -}.
Proof.
Admitted.

Lemma DTOrEntails C Z H1 H2 A :
  Z ||- C, {-A always (H1 \/ H2) -} ->
  Z ||- C, {-A H1 =>> A -} ->
  Z ||- C, {-A H2 =>> A -} ->
  Z ||- C, {-A always A -}.
Proof.
Admitted.

Lemma DTOrEntailsP C Delta H1 H2 A :
  Context Delta [::] ||- C, {-A
    (H1 =>> A) /\ (H2 =>> A) ->
    (H1 \/ H2 =>> A)
  -}.
Proof.
Admitted.
Ltac dtorentailsp_c :=
  match goal with
  | |- context[ {-A ?H1_ \/ ?H2_ =>> ?A_ -} ] =>
    eapply DSCut; first (by repeat dclear; apply DTOrEntailsP with
      (H1 := H1_) (H2 := H2_) (A := A_))
  end.

Lemma DTEntailsOrTautL C Z H A1 A2 :
  Z ||- C, {-A H =>> A2 -} ->
  Z ||- C, {-A H =>> A1 \/ A2 -}.
Proof.
Admitted.

Lemma DTEntailsOrTautR C Z H A1 A2 :
  Z ||- C, {-A H =>> A2 -} ->
  Z ||- C, {-A H =>> A1 \/ A2 -}.
Proof.
Admitted.

Lemma DTEntailsAlwaysC C Z H A :
  Z ||- C, {-A always A -} ->
  Z ||- C, {-A H =>> A -}.
Proof.
Admitted.

Lemma DTAndComm C Delta A1 A2 :
  Context Delta [::] ||- C, {-A
    (A1 /\ A2) <=> (A2 /\ A1)
  -}.
Proof.
Admitted.

Lemma DTAndAssoc C Delta A1 A2 A3 :
  Context Delta [::] ||- C, {-A
    (A1 /\ A2) /\ A3 <=>
    A1 /\ (A2 /\ A3)
  -}.
Proof.
Admitted.
Ltac dtandassoc_l :=
  match goal with
  | |- context[ {-A (?A1_ /\ ?A2_) /\ ?A3_ -} ] =>
    eapply DSCut; first (by repeat dclear; apply DTAndAssoc with
      (A1 := A1_) (A2 := A2_) (A3 := A3_))
  end.

Lemma DTAndExampleExists C Delta H1 H2 x :
  Context Delta [::] ||- C, {-A
    ((forall: H1) ' x /\ exists: H1 /\ H2) =>>
    (forall: H2) ' x
  -}.
Proof.
Admitted.

Lemma DTExistsConstant C Delta A :
  assertion_closed_in [::] Delta A ->
  Context Delta [::] ||- C, {-A
    A <=> exists: A
  -}.
Proof.
Admitted.

Lemma DTAndIntoExists C Delta A1 A2 :
  assertion_closed_in [::] Delta A1 ->
  Context Delta [::] ||- C, {-A
    (A1 /\ exists: A2) =>>
    exists: push_assertion_params A1 /\ A2
  -}.
Proof.
Admitted.

Ltac dtandintoexists :=
  match goal with
  | |- context[ {-A ?A1_ /\ exists: ?A2_ -} ] =>
    eapply DSCut; first (by repeat dclear; eapply DTAndIntoExists with
      (A1 := A1_) (A2 := A2_); first by dautoclosed);
    rewrite /push_assertion_params /=; dclean
  end.

Lemma DTAndHA_L C Delta A' H A :
  Context Delta [::] ||- C, {-A
    (A' /\ H =>> A' /\ A) <=>
    (H =>> A)
  -}.
Proof.
Admitted.

Ltac dtandha_l :=
  match goal with
  | |- Context _ _ ||- _, {-A ?A'_ /\ ?H_ =>> ?A'_ /\ ?A_ -} =>
    eapply DSCut; first (by repeat dclear; apply DTAndHA_L with
      (A' := A'_) (H := H_) (A := A_))
  end.

Lemma DTAndHA_R C Delta A' H A :
  Context Delta [::] ||- C, {-A
    (H /\ A' =>> A /\ A') <=>
    (H =>> A)
  -}.
Proof.
Admitted.

Lemma DTConcludeHypothesis C Delta H1 H2 A :
  Context Delta [::] ||- C, {-A
    (H1 /\ H2 =>> A) <=>
    (H1 /\ H2 =>> H1 /\ A)
  -}.
Proof.
Admitted.
Ltac dtconclhyp_intro_p :=
  match goal with
  | |- Context _ ({-A ?H1_ /\ ?H2_ =>> ?A_ -} :: _) ||- _, _ =>
    eapply DSCut; first (by repeat dclear; apply DTConcludeHypothesis with
      (H1 := H1_) (H2 := H2_) (A := A_));
    dsplitp; dswap; dclear;
    dsplitp; dswap; dclear;
    difp; first by []
  end.

Lemma DTOrDistrib2 C Delta A1 A2 A3 :
  Context Delta [::] ||- C, {-A
    A1 /\ (A2 \/ A3) <=>
    (A1 /\ A2) \/ (A1 /\ A3)
  -}.
Proof.
Admitted.

Lemma DTOrElimSelf C Delta A :
  Context Delta [::] ||- C, {-A
    A \/ A <=> A
  -}.
Proof.
Admitted.

Lemma DTOrComm C Z H1 H2 :
  Z ||- C, {-A (H1 \/ H2) <=> (H2 \/ H1) -}.
Proof.
Admitted.

Lemma DTAlwaysAlways' C Z A :
  Z ||- C, {-A always A =>> always^ A -}.
Proof.
  by dtentails_r.
Qed.

Lemma DTMergeEntailsIf C Delta H1 H2 A :
  Context Delta [::] ||- C, {-A (H1 =>> H2 -> A) =>> (H1 /\ H2 =>> A) -}.
Proof.
Admitted.

Lemma DTMergeIf C Delta Gamma H1 H2 A :
  Context Delta Gamma ||- C, {-A
    (H1 -> H2 -> A)
    <=>
    (H1 /\ H2 -> A)
   -}.
Proof.
Admitted.

Lemma DTAndImplies C Delta A1 A2 :
  Context Delta [::] ||- C, {-A
    (A1 /\ A2) =>> (A1 -> A2)
  -}.
Proof.
Admitted.

Lemma DTEntailsTrue C Delta H :
  Context Delta [::] ||- C, {-A
    (H =>> ATrue) <=> ATrue
  -}.
Proof.
Admitted.
Ltac dtentailstrue_l :=
  match goal with
  | |- context[ {-A ?H_ =>> ATrue -} ] =>
    eapply DSCut; first (by repeat dclear; apply DTEntailsTrue with
      (H := H_))
  end.

Lemma DTSelfTrue C Delta :
  Context Delta [::] ||- C, {-A
    self ATrue
  -}.
Proof.
Admitted.

Lemma DTEventuallyPAlways C Delta A :
  assertion_rigid A ->
  non_temporal_assertion A ->
  Context Delta [::] ||- C, {-A
    eventuallyp A =>> always A
  -}.
Proof.
Admitted.

(* Further tactics *)
Ltac dtsubstp_l_keep :=
  match goal with
  | |- Context _ (?R_ :: ?H_ :: _) ||- _, _ =>
    eapply DSCut; [eapply DTSubstR with (R := R_) (A := H_);
      [by dsplitimpl | by dunify | by [] | by [] | by [] ] |
    dclean; do 2 (dsplitp; dswap; dclear); difp; first by dassumption]
  end.
Ltac dtsubstp_l := dtsubstp_l_keep; do 2 (dswap; dclear).
Ltac dtsubstp_r_keep :=
  match goal with
  | |- Context _ (?R_ :: ?H_ :: _) ||- _, _ =>
    eapply DSCut; [eapply DTSubstL with (R := R_) (A := H_);
      [by dsplitimpl | by dunify | by [] | by [] | by [] ] |
    dclean; do 2 (dsplitp; dswap; dclear); difp; first by dassumption]
  end.
Ltac dtsubstp_r := dtsubstp_r_keep; do 2 (dswap; dclear).
Ltac dtsubst_l :=
  match goal with
  | |- Context _ (?R_ :: _) ||- _, ?A_ =>
    eapply DSCut; [eapply DTSubstL with (R := R_) (A := A_);
      [by dsplitimpl | by dunify | by [] | by [] | by [] ] |
    dclean; dsplitp; dswap; dclear; dsplitp; dclear; difp; last by dassumption]
  end.
Ltac dtsubst_r :=
  match goal with
  | |- Context _ (?R_ :: _) ||- _, ?A_ =>
    eapply DSCut; [eapply DTSubstR with (R := R_) (A := A_);
      [by dsplitimpl | by dunify | by[] | by [] | by [] ] |
    dclean; dsplitp; dswap; dclear; dsplitp; dclear; difp; last by dassumption]
  end.
Ltac dtreple_cl :=
  rewrite /AOn /TFlexible /TRigid; (* Commonly needed for equality *)
  match goal with
  | |- _ ||- _, {-A ?t1_ = ?t2_ =>> ?A_ -} =>
    eapply DSCut;
      [eapply DTReplE' with (t1 := t1_) (t2 := t2_) (A := A_);
        [try by repeat constructor | try by rewrite /term_rigid //=; auto] |]
  end;
  dclean;
  dsplitp; dswap; dclear;
  dsplitp; dclear;
  difp; last (by dassumption).
Ltac dtifsubste_pl :=
  rewrite /AOn /TFlexible /TRigid; (* Commonly needed for equality *)
  match goal with
  | |- Context _ ({-A ?H_ =>> ?A_ -} :: _) ||- _,
    {-A TVariable ?x1 = TVariable ?x2 /\ ?H_ =>> _ -} =>
    eapply DSCut; [eapply DTIfSubstE with
      (x := x1) (t1 := x1) (t2 := x2) (H := H_) (A := A_) |];
      [by repeat auto_mem | by [] | by [] |]
  end;
  dclean; dsplitp; dswap; dclear; dsplitp; dswap; dclear; difp;
    (try by []); (try by dtentails_r).
Ltac dtifsubste' :=
  match goal with
  | |- Context _ _ ||- _, {-A ?H_ =>> ?A_ -} =>
    eapply DSCut; first (by repeat dclear; apply DTIfSubstE' with
      (H := H_) (A := A_)); dclean; dsplitp; dswap; dclear
  end.
Ltac dtsubstep_l :=
  rewrite /AOn /TFlexible /TRigid; (* Commonly needed for equality *)
  match goal with
  | |- Context _ ({-A always (?t1_ = ?t2_) -} :: ?H_ :: _) ||- _, _ =>
    eapply DSCut;
      [eapply DTSubstE' with (t1 := t1_) (t2 := t2_) (A := H_);
        [try by rewrite /term_rigid //=; auto] |]
  end;
  dclean; difp; first (by dassumption);
  dsplitp; dswap; dclear;
  dsplitp; dswap; dclear;
  difp; first (by dassumption);
  dxchg 0 2; dclear; dswap.
Ltac dtsubste_l :=
  rewrite /AOn /TFlexible /TRigid; (* Commonly needed for equality *)
  match goal with
  | |- Context _ ({-A always (?t1_ = ?t2_) -} :: _) ||- _, ?A_ =>
    eapply DSCut;
      [eapply DTSubstE' with (t1 := t1_) (t2 := t2_) (A := A_);
        [try by rewrite /term_rigid //=; auto] |]
  end;
  dclean; difp; first (by dassumption);
  dsplitp; dswap; dclear;
  dsplitp; dclear;
  difp; (try by []).

Ltac dtmergeentailsifp :=
  match goal with
  | |- Context _ ({-A ?H1_ =>> ?H2_ -> ?A_ -} :: _) ||- _, _ =>
    eapply DSCut; first (by repeat dclear; apply DTMergeEntailsIf with
      (H1 := H1_) (H2 := H2_) (A := A_)); dtsubstposp
  end.
Ltac dtmergeif :=
  match goal with
  | |- context[ {-A ?H1_ -> ?H2_ -> ?A_ -} ] =>
    eapply DSCut; first (by repeat dclear; apply DTMergeIf with
      (H1 := H1_) (H2 := H2_) (A := A_))
  end.

Ltac dtandelimselfap :=
  match goal with
  | |- context[ {-A ?A1_ /\ (?A1_ /\ ?A2_) -} ] =>
    eapply DSCut; first (by repeat dclear; eapply DSAndAssoc with
      (A1 := A1_) (A2 := A1_) (A3 := A2_));
    dtgenp; dclean; dtsubstp_r;
    eapply DSCut; first (by repeat dclear; eapply DSAndElimSelf with
      (A := A1_));
    dtgenp; dclean; dtsubstp_l
  end; dclean.

Ltac dtordistrib2_2 :=
  match goal with
  | |- context[ {-A ?A1_ /\ (?A2_ \/ ?A3_) -} ] =>
    eapply DSCut; first (by repeat dclear; apply DTOrDistrib2 with
      (A1 := A1_) (A2 := A2_) (A3 := A3_)); dtsubstp_l;
    eapply DSCut; first (by repeat dclear; apply DTEntailsAndDropLeft with
      (A1 := A1_) (A2 := A2_)); dtsubstposp
  end.
