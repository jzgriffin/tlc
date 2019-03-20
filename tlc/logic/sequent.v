(* TLC in Coq
 *
 * Module: tlc.logic.sequent
 * Purpose: Contains derived rules and lemmas regarding sequents.
 *)

Require Import mathcomp.ssreflect.eqtype.
Require Import mathcomp.ssreflect.seq.
Require Import mathcomp.ssreflect.ssrbool.
Require Import mathcomp.ssreflect.ssreflect.
Require Import mathcomp.ssreflect.ssrnat.
Require Import tlc.component.component.
Require Import tlc.logic.context.
Require Import tlc.logic.derives.
Require Import tlc.operation.orientation.
Require Import tlc.operation.periodic_event.
Require Import tlc.semantics.all_semantics.
Require Import tlc.syntax.all_syntax.
Require Import tlc.utility.result.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Rule for applying axioms in any position *)
Lemma DSAssumption C Delta Gamma A :
  A \in Gamma ->
  Context Delta Gamma |- C, A.
Proof.
  elim: Gamma => [| Ap Gamma IHC] //=; rewrite in_cons;
    case HA: (A == Ap); move/eqP: HA => HA; subst; rewrite //=.
  by move/IHC => H; d_clear.
Qed.

Tactic Notation "d_assumption" := eapply DSAssumption.

(* Rule for rotating the set of assumptions *)
Lemma DSRotate C Delta Gamma n Ac :
  Context Delta (rot n Gamma) |- C, Ac ->
  Context Delta Gamma |- C, Ac.
Proof.
  (* Provable by DSExchange *)
Admitted. (* TODO *)

Tactic Notation "d_rotate" constr(x) :=
  apply DSRotate with (n := x); rewrite /rot /=.
Tactic Notation "d_rotate" := d_rotate 1.

(* Rule for removing duplicate premises *)
Lemma DSUnique C Delta Gamma Ac :
  Context Delta (undup Gamma) |- C, Ac ->
  Context Delta Gamma |- C, Ac.
Proof.
  (* Provable by DSThin *)
Admitted. (* TODO *)

(* Modus ponens in the conclusion *)
Lemma DSModusPonensC C ctx Ap Ac :
  ctx |- C, Ap ->
  ctx |- C, {A: Ap -> Ac} ->
  ctx |- C, Ac.
Proof.
  case: ctx => [Delta Gamma] Hl H.
  apply DSCut with (Ap := Ap); first by [].
  apply DSCut with (Ap := {A: Ap -> Ac}); first by d_clear.
  by d_ifp.
Qed.

(* Temporal modus ponens in the premise *)
Lemma DSEntailsModusPonensP C Delta Gamma App Apc Ac :
  Context Delta Gamma |- C, App ->
  Context Delta (Apc :: Gamma) |- C, Ac ->
  Context Delta ({A: App =>> Apc} :: Gamma) |- C, Ac.
Proof.
  move=> H1 H2.
  by d_splitp; d_swap; d_clear; d_ifp.
Qed.

(* Temporal modus ponens in the conclusion *)
Lemma DSEntailsModusPonensC C Delta Gamma Ap Ac :
  Context Delta Gamma |- C, Ap ->
  Context Delta Gamma |- C, {A: Ap =>> Ac} ->
  Context Delta Gamma |- C, Ac.
Proof.
  move=> Hl H.
  apply DSCut with (Ap := Ap); first by [].
  apply DSCut with (Ap := {A: Ap -> Ac});
    first by apply DSThin, (DSModusPonensC H (DT1 _ _ {A: Ap -> Ac})).
  by d_ifp.
Qed.

(* Elimination of And with True *)
Lemma DSAndElimination C ctx A :
  ctx |- C, {A: A /\ ATrue <-> A}.
Proof.
  case: ctx => Delta Gamma.
  d_splitc; d_ifc.
  - by d_splitp.
  - by d_splitc; first by []; last by d_notc.
Qed.

(* Elimination of Or with False *)
Lemma DSOrElimination C ctx A :
  ctx |- C, {A: A \/ AFalse <-> A}.
Proof.
  case: ctx => Delta Gamma.
  by d_splitc; d_ifc; [d_orp | d_left].
Qed.

(* Commutativity of And *)
Lemma DSAndCommutative C ctx Acl Acr :
  ctx |- C, {A: (Acl /\ Acr) <-> (Acr /\ Acl)}.
Proof.
  case: ctx => Delta Gamma.
  by d_splitc; d_ifc; d_splitp; d_splitc; try by []; by d_clear.
Qed.

(* Commutativity of Or *)
Lemma DSOrCommutative C ctx Acl Acr :
  ctx |- C, {A: (Acl \/ Acr) <-> (Acr \/ Acl)}.
Proof.
  case: ctx => Delta Gamma.
  by d_splitc; d_ifc; d_orp; (try by d_left); (try by d_right).
Qed.

(* Commutativity of Iff *)
Lemma DSIffCommutative C ctx Acl Acr :
  ctx |- C, {A: (Acl <-> Acr) <-> (Acr <-> Acl)}.
Proof.
  by apply DSAndCommutative.
Qed.

(* Commutativity of Congruent *)
Lemma DSCongruentCommutative C ctx Acl Acr :
  ctx |- C, {A: (Acl <=> Acr) <-> (Acr <=> Acl)}.
Proof.
  by apply DSAndCommutative.
Qed.

(* The premises of nested implications can be merged into a single
 * implication where the premise is the conjunction of the premises
 *)
Lemma DSMergeIf C Delta Gamma Ap1 Ap2 Ac :
  Context Delta Gamma |- C, {A:
    (Ap1 -> Ap2 -> Ac)
    <->
    (Ap1 /\ Ap2 -> Ac)
  }.
Proof.
  d_splitc.
  - d_ifc; d_ifc; d_splitp; d_rotate 2.
    d_ifp; first by d_assumption; rewrite mem_cat; apply/orP; right;
      rewrite in_cons; apply/orP; left.
    d_ifp; first by d_assumption; rewrite mem_cat; apply/orP; right;
      rewrite in_cons; apply/orP; right;
      rewrite mem_seq1.
    by d_head.
  - d_ifc; d_ifc; d_ifc; d_rotate 2.
    d_ifp.
      d_splitc.
      - by d_assumption; rewrite mem_cat; apply/orP; right;
          rewrite in_cons; apply/orP; right;
          rewrite mem_seq1.
      - by d_assumption; rewrite mem_cat; apply/orP; right;
          rewrite in_cons; apply/orP; left.
    by d_head.
Qed.

(* Negation is the same as implication with a false conclusion *)
Lemma DSNotImpliesFalse C ctx Ac :
  ctx |- C, {A: ~Ac <-> (Ac -> AFalse)}.
Proof.
  case: ctx => Delta Gamma.
  d_splitc; d_ifc.
  - by d_ifc; d_swap; d_notp.
  - d_notc; d_swap; d_notp; d_splitc.
    + by d_notc; d_notp.
    + by d_notc.
Qed.

Lemma DSIfAndSplit C ctx Ap Acl Acr :
  ctx |- C, {A: ((Ap -> Acl) /\ (Ap -> Acr)) <-> (Ap -> (Acl /\ Acr))}.
Proof.
  case: ctx => Delta Gamma.
  d_splitc; d_ifc.
  - d_splitp; d_ifc; d_splitc.
    + by d_swap; d_ifp; first by d_head.
    + by d_swap; d_clear; d_swap; d_ifp; first by d_head.
  - d_splitc; d_ifc; d_swap; (d_ifp; first by d_head); d_splitp.
    + by d_head.
    + by d_swap.
Qed.

Lemma DSIfAndIntroduce C ctx Apl Apr Ac :
  ctx |- C, {A: (Apl /\ Apr -> Ac) <-> (Apl /\ Apr -> Apl /\ Ac)}.
Proof.
  case: ctx => Delta Gamma.
  d_splitc; d_ifc; d_ifc.
  - d_splitc.
    + by d_splitp; d_head.
    + by d_swap; d_ifp.
  - d_swap; d_ifp; first by d_head. by d_splitp; d_swap.
Qed.

Lemma DSIfAndEliminate C ctx Ap Acl Acr :
  ctx |- C, {A: (Ap -> (Acl /\ Acr)) -> (Ap -> Acl)}.
Proof.
  case: ctx => Delta Gamma.
  d_ifc; d_ifc; d_swap; d_ifp; first by d_head.
  by d_splitp; d_head.
Qed.

Lemma DSOrDistributesAnd C ctx Al Ar A :
  ctx |- C, {A: A /\ (Al \/ Ar) <-> (A /\ Al) \/ (A /\ Ar)}.
Proof.
  case: ctx => Delta Gamma.
  d_splitc; d_ifc.
  - d_splitp; d_swap; d_orp.
    + by d_left; d_splitc; [d_clear; d_head | d_head].
    + by d_right; d_splitc; [d_clear; d_head | d_head].
  - d_splitc.
    + by d_orp; d_splitp; d_head.
    + by d_orp; d_splitp; d_clear; [d_left | d_right].
Qed.

Lemma DSAndAssociative C ctx Al Am Ar :
  ctx |- C, {A: (Al /\ Am) /\ Ar <-> Al /\ (Am /\ Ar)}.
Proof.
  case: ctx => Delta Gamma.
  d_splitc; d_ifc.
  - d_splitp; d_splitp.
    d_splitc; first by d_head.
    d_clear; d_splitc; first by d_head.
    by d_clear; d_head.
  - d_splitp; d_swap; d_splitp.
    d_splitc.
    + d_splitc.
      * by d_clear; d_clear; d_head.
      * by d_head.
    + by d_clear; d_head.
Qed.
