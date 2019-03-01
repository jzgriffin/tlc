Require Import mathcomp.ssreflect.eqtype.
Require Import mathcomp.ssreflect.seq.
Require Import mathcomp.ssreflect.ssrbool.
Require Import mathcomp.ssreflect.ssreflect.
Require Import mathcomp.ssreflect.ssrnat.
Require Import tlc.component.component.
Require Import tlc.logic.derives.
Require Import tlc.operation.orientation.
Require Import tlc.operation.periodic_event.
Require Import tlc.semantics.all_semantics.
Require Import tlc.syntax.all_syntax.
Require Import tlc.utility.result.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Derived sequent rules and lemmas *)

(* Extension for applying axioms in any position *)
Lemma DAnyAxiom C Gamma A :
  A \in Gamma ->
  Gamma |- C, A.
Proof.
  elim: Gamma => [| Ap Gamma IHC] //=; rewrite in_cons;
    case HA: (A == Ap); move/eqP: HA => HA; subst; rewrite //=.
  by move/IHC => H; apply DSThin.
Qed.

(* Rule for rotating the premise set *)
Lemma DSRotate C Gamma n Ac :
  rot n Gamma |- C, Ac ->
  Gamma |- C, Ac.
Proof.
  (* Provable by DSExchange *)
Admitted. (* TODO *)

(* Rule for removing duplicate premises *)
Lemma DSUnique C Gamma Ac :
  undup Gamma |- C, Ac ->
  Gamma |- C, Ac.
Proof.
  (* Provable by DSThin *)
Admitted. (* TODO *)

Lemma DModusPonensC C Gamma Ap Ac :
  Gamma |- C, Ap ->
  Gamma |- C, {A: Ap -> Ac} ->
  Gamma |- C, Ac.
Proof.
  move=> Hl H.
  apply DSCut with (Ap := Ap); first by [].
  apply DSCut with (Ap := {A: Ap -> Ac}); first by apply DSThin.
  by apply DSIfP.
Qed.

Lemma DEntailsModusPonensP C Gamma App Apc Ac :
  Gamma |- C, App ->
  Apc :: Gamma |- C, Ac ->
  {A: App =>> Apc} :: Gamma |- C, Ac.
Proof.
  move=> H1 H2.
  apply DSAndP, DSExchange, DSThin.
  by apply DSIfP.
Qed.

Lemma DEntailsModusPonensC C Gamma Ap Ac :
  Gamma |- C, Ap ->
  Gamma |- C, {A: Ap =>> Ac} ->
  Gamma |- C, Ac.
Proof.
  move=> Hl H.
  apply DSCut with (Ap := Ap); first by [].
  apply DSCut with (Ap := {A: Ap -> Ac});
    first by apply DSThin, (DModusPonensC H (DT1 _ _ {A: Ap -> Ac})).
  by apply DSIfP.
Qed.

(* Elimination of And with True *)
Lemma DAndElimination C Gamma A :
  Gamma |- C, {A: A /\ ATrue <-> A}.
Proof.
  apply DSAndC.
  - by apply DSIfC, DSAndP.
  - apply DSIfC, DSAndC; first by [].
    by apply DSNotC.
Qed.

(* Elimination of Or with False *)
Lemma DOrElimination C Gamma A :
  Gamma |- C, {A: A \/ AFalse <-> A}.
Proof.
  apply DSAndC.
  - by apply DSIfC, DSOrP.
  - by apply DSIfC, DSOrCL.
Qed.

(* Commutativity of Or *)
Lemma DOrCommutative C Gamma Acl Acr :
  Gamma |- C, {A: Acl \/ Acr} ->
  Gamma |- C, {A: Acr \/ Acl}.
Proof.
  move=> H.
  apply DSCut with (Ap := {A: Acl \/ Acr}); first by [].
  apply DSOrP.
  - by apply DSOrCR, DSAxiom.
  - by apply DSOrCL, DSAxiom.
Qed.

(* Commutativity of And *)
Lemma DAndCommutative C Gamma Acl Acr :
  Gamma |- C, {A: Acl /\ Acr} ->
  Gamma |- C, {A: Acr /\ Acl}.
Proof.
  move=> H.
  apply DSCut with (Ap := {A: Acl /\ Acr}); first by [].
  apply DSAndP, DSAndC.
  - by apply DSExchange, DSAxiom.
  - by apply DSAxiom.
Qed.

(* Commutativity of Iff *)
Lemma DIffCommutative C Gamma Acl Acr :
  Gamma |- C, {A: Acl <-> Acr} ->
  Gamma |- C, {A: Acr <-> Acl}.
Proof.
  by apply DAndCommutative.
Qed.

(* Commutativity of Congruent *)
Lemma DCongruentCommutative C Gamma Acl Acr :
  Gamma |- C, {A: Acl <=> Acr} ->
  Gamma |- C, {A: Acr <=> Acl}.
Proof.
  by apply DAndCommutative.
Qed.

Lemma DEntailsIf C Gamma Acl Acr :
  Gamma |- C, {A: Acl =>> Acr} ->
  Gamma |- C, {A: Acl -> Acr}.
Proof.
  move=> H.
  have H' : Gamma |- C, {A: (Acl =>> Acr) -> (Acl -> Acr)} by apply DT1.
  by apply (DModusPonensC H H').
Qed.

Lemma DCongruentIff C Gamma Acl Acr :
  Gamma |- C, {A: Acl <=> Acr} ->
  Gamma |- C, {A: Acl <-> Acr}.
Proof.
  move=> H.
  apply DSAndC.
  - have Hl : Gamma |- C, {A: Acl =>> Acr} by
      apply DSCut with (Ap := {A: Acl <=> Acr}); first by [];
      by apply DSAndP.
    by apply (DEntailsIf Hl).
  - have Hr : Gamma |- C, {A: Acr =>> Acl} by
      apply DSCut with (Ap := {A: Acl <=> Acr}); first by [];
      by apply DSAndP, DSExchange.
    by apply (DEntailsIf Hr).
Qed.
