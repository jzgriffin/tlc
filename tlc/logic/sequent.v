(* TLC in Coq
 *
 * Module: tlc.logic.sequent
 * Purpose: Contains derived rules and lemmas regarding sequents.
 *)

Require Import Coq.Strings.String.
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
Require Import tlc.utility.seq.
Require Import tlc.utility.result.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section variable_context.

  (* Rule for exchanging the head variables *)
  Lemma DVSwap C Delta Gamma x1 x2 A :
    Context (x1 :: x2 :: Delta) Gamma ||- C, A ->
    Context (x2 :: x1 :: Delta) Gamma ||- C, A.
  Proof.
    by apply DVExchange with (Delta1 := [::]) (Delta2 := Delta).
  Qed.

  Tactic Notation "dvswap" := apply DVSwap.

  (* Rule for exchanging with the head variable by index *)
  Lemma DVExchangeIndex C Delta Gamma A x0 i xi :
    ohead Delta = Some x0 ->
    onth Delta i = Some xi ->
    Context (set_nth (R EmptyString) (set_nth (R EmptyString) Delta i x0) 0 xi)
      Gamma ||- C, A ->
    Context Delta Gamma ||- C, A.
  Proof.
  Admitted.

  Ltac dvxchg0 j := eapply DVExchangeIndex with (i := j); [by [] | by [] | simpl].
  Ltac dvxchg i j := dvxchg0 i; dvxchg0 j; dvxchg0 i.

  (* Rule for removing duplicate variables *)
  Lemma DVUnique C Delta Gamma A :
    Context (undup Delta) Gamma ||- C, A ->
    Context Delta Gamma ||- C, A.
  Proof.
    (* Provable by DVThin *)
  Admitted.

End variable_context.

(* Rule for applying axioms in any position *)
Lemma DSAssumption C Delta Gamma A :
  A \in Gamma ->
  Context Delta Gamma ||- C, A.
Proof.
  elim: Gamma => [| H Gamma IH] //=; rewrite in_cons;
  case: eqP => [<- | _] //=.
  by move/IH => HA; dclear.
Qed.

Tactic Notation "dassumption" := eapply DSAssumption; repeat auto_mem.

(* Rule for exchanging the head assumptions *)
Lemma DSSwap C Delta Gamma H1 H2 A :
  Context Delta (H1 :: H2 :: Gamma) ||- C, A ->
  Context Delta (H2 :: H1 :: Gamma) ||- C, A.
Proof.
  by apply DSExchange with (Gamma1 := [::]) (Gamma2 := Gamma).
Qed.

Tactic Notation "dswap" := apply DSSwap.

(* Rule for exchanging with the head assumption by index *)
Lemma DSExchangeIndex C Delta Gamma A H0 i Hi :
  ohead Gamma = Some H0 ->
  onth Gamma i = Some Hi ->
  Context Delta (set_nth AFalse (set_nth AFalse Gamma i H0) 0 Hi) ||- C, A ->
  Context Delta Gamma ||- C, A.
Proof.
Admitted.

Ltac dxchg0 j := eapply DSExchangeIndex with (i := j); [by [] | by [] | simpl].
Ltac dxchg i j := dxchg0 i; dxchg0 j; dxchg0 i.
Ltac dexacti i := by dxchg0 i; dhead.

(* Rule for removing duplicate premises *)
Lemma DSUnique C Delta Gamma A :
  Context Delta (undup Gamma) ||- C, A ->
  Context Delta Gamma ||- C, A.
Proof.
  (* Provable by DSThin *)
Admitted.

(* Law of the excluded middle
 * By restructuring the sequent rules in the derives type, this could be proven
 * directly.  For now, however, it is simplest to admit it as an axiom.
 *)
Axiom DSEM :
  forall C Z A,
  Z ||- C, {-A A \/ ~A -}.

(* True can always be proven *)
Lemma DSTrue C Delta Gamma :
  Context Delta Gamma ||- C, ATrue.
Proof.
  by dnot.
Qed.

Hint Resolve DSTrue : core.

(* Negation is the same as implication with a false conclusion *)
Lemma DSNotImpliesFalse C Delta Gamma A :
  Context Delta Gamma ||- C, {-A ~A <-> (A -> AFalse) -}.
Proof.
  dsplit; dif.
  - by dif; dswap; dnotp.
  - by dnot; dswap; dnotp; dsplit; dnot; [dnotp |].
Qed.

(* Modus ponens in the premise *)
Lemma DSMPP C Delta Gamma Hp Hc A :
  Context Delta Gamma ||- C, Hp ->
  Context Delta (Hc :: Gamma) ||- C, A ->
  Context Delta ({-A Hp -> Hc -} :: Gamma) ||- C, A.
Proof.
  move=> H1 H2.
  by difp; [apply H1 | apply H2].
Qed.

(* Modus ponens in the conclusion *)
Lemma DSMPC C Delta Gamma H A :
  Context Delta Gamma ||- C, {-A H -> A -} ->
  Context Delta Gamma ||- C, H ->
  Context Delta Gamma ||- C, A.
Proof.
  move=> HHA HH.
  apply DSCut with (H := H); first by [].
  apply DSCut with (H := {-A H -> A -}); first by dclear.
  by difp.
Qed.

(* Commutativity of And *)
Lemma DSAndComm C Delta Gamma A1 A2 :
  Context Delta Gamma ||- C, {-A (A1 /\ A2) <-> (A2 /\ A1) -}.
Proof.
  by dsplit; dif; dsplitp; dsplit; try by []; by dclear.
Qed.

(* Associativity of And *)
Lemma DSAndAssoc C Delta Gamma A1 A2 A3 :
  Context Delta Gamma ||- C, {-A
    (A1 /\ A2) /\ A3 <->
    A1 /\ (A2 /\ A3)
  -}.
Proof.
  dsplit; dif.
  - by dsplitp; dsplitp; dsplit; [| dsplit]; dassumption.
  - by dsplitp; dswap; dsplitp; dsplit; [dsplit |]; dassumption.
Qed.

(* Elimination of And with True *)
Lemma DSAndElimTL C Delta Gamma A :
  Context Delta Gamma ||- C, {-A ATrue /\ A <-> A -}.
Proof.
  dsplit; dif.
  - by dsplitp; dassumption.
  - by dsplit; first by dnot.
Qed.

Lemma DSAndElimTR C Delta Gamma A :
  Context Delta Gamma ||- C, {-A A /\ ATrue <-> A -}.
Proof.
  dsplit; dif.
  - by dsplitp.
  - by dsplit; last by dnot.
Qed.

(* Elimination of And with False *)
Lemma DSAndElimFL C Delta Gamma A :
  Context Delta Gamma ||- C, {-A AFalse /\ A <-> AFalse -}.
Proof.
  dsplit; dif.
  - by dsplitp.
  - by dsplit.
Qed.

Lemma DSAndElimFR C Delta Gamma A :
  Context Delta Gamma ||- C, {-A A /\ AFalse <-> AFalse -}.
Proof.
  dsplit; dif.
  - by dsplitp; dassumption.
  - by dsplit.
Qed.

(* Commutativity of Or *)
Lemma DSOrComm C Delta Gamma Acl Acr :
  Context Delta Gamma ||- C, {-A (Acl \/ Acr) <-> (Acr \/ Acl) -}.
Proof.
  by dsplit; dif; dorp; (try by dleft); (try by dright).
Qed.

(* Elimination of Or with True *)
Lemma DSOrElimTL C Delta Gamma A :
  Context Delta Gamma ||- C, {-A ATrue \/ A <-> ATrue -}.
Proof.
  by dsplit; dif; [dorp | dleft]; dnot.
Qed.

Lemma DSOrElimTR C Delta Gamma A :
  Context Delta Gamma ||- C, {-A A \/ ATrue <-> ATrue -}.
Proof.
  by dsplit; dif; [dorp | dright]; dnot.
Qed.

(* Elimination of Or with False *)
Lemma DSOrElimFL C Delta Gamma A :
  Context Delta Gamma ||- C, {-A AFalse \/ A <-> A -}.
Proof.
  by dsplit; dif; [dorp | dright].
Qed.

Lemma DSOrElimFR C Delta Gamma A :
  Context Delta Gamma ||- C, {-A A \/ AFalse <-> A -}.
Proof.
  by dsplit; dif; [dorp | dleft].
Qed.

(* Commutativity of Iff *)
Lemma DSIffComm C Delta Gamma A1 A2 :
  Context Delta Gamma ||- C, {-A (A1 <-> A2) <-> (A2 <-> A1) -}.
Proof.
  by exact: DSAndComm.
Qed.

(* The premises of nested implications can be merged into a single implication
 * where the premise is the conjunction of the premises
 *)
Lemma DSMergeIf C Delta Gamma H1 H2 A :
  Context Delta Gamma ||- C, {-A
    (H1 -> H2 -> A)
    <->
    (H1 /\ H2 -> A)
   -}.
Proof.
  dsplit.
  - by dif; dif; dsplitp; dxchg0 2; difp; [| difp]; dassumption.
  - by dif; dif; dif; dxchg0 2; difp; [dsplit |]; dassumption.
Qed.

Lemma DSIfAndDropL C Delta Gamma A1 A2 :
  Context Delta Gamma ||- C, {-A
    A1 /\ A2 -> A2
   -}.
Proof.
  by dif; dsplitp; dswap.
Qed.

Lemma DSIfAndDropR C Delta Gamma A1 A2 :
  Context Delta Gamma ||- C, {-A
    A1 /\ A2 -> A1
   -}.
Proof.
  by dif; dsplitp.
Qed.

Lemma DSIfMergeAnd C Delta Gamma H A1 A2 :
  Context Delta Gamma ||- C, {-A
    (H -> A1) /\ (H -> A2) ->
    (H -> A1 /\ A2)
   -}.
Proof.
  dif; dsplitp; dif; dsplit.
  - dswap; difp; by [].
  - dswap; dclear; dswap; difp; by [].
Qed.

Lemma DSIfAndSplit C Delta Gamma H A1 A2 :
  Context Delta Gamma ||- C, {-A
    ((H -> A1) /\ (H -> A2)) <->
    (H -> (A1 /\ A2))
  -}.
Proof.
  dsplit; dif.
  - dsplitp; dif; dsplit.
    + by dswap; difp; first by dhead.
    + by dswap; dclear; dswap; difp; first by dhead.
  - dsplit; dif; dswap; (difp; first by dhead); dsplitp.
    + by dhead.
    + by dswap.
Qed.

Lemma DSIfAndIntro C Delta Gamma H1 H2 A :
  Context Delta Gamma ||- C, {-A
    (H1 /\ H2 -> A) <->
    (H1 /\ H2 -> H1 /\ A)
  -}.
Proof.
  dsplit; dif; dif.
  - by dsplit; [dsplitp | dswap; difp].
  - by dswap; difp; [| dsplitp]; dassumption.
Qed.

Lemma DSIfAndElim C Delta Gamma H A1 A2 :
  Context Delta Gamma ||- C, {-A
    (H -> (A1 /\ A2)) ->
    (H -> A1)
  -}.
Proof.
  by dif; dif; dswap; difp; [| dsplitp].
Qed.

Lemma DSOrDistribAnd2 C Delta Gamma A A1 A2 :
  Context Delta Gamma ||- C, {-A
    A /\ (A1 \/ A2) <-> (A /\ A1) \/ (A /\ A2)
  -}.
Proof.
  dsplit; dif.
  - by dsplitp; dswap; dorp; [dleft | dright]; dsplit; dassumption.
  - by dsplit; dorp; dsplitp; (try by []); [dleft | dright]; dassumption.
Qed.

Lemma DSOrDistribAnd3 C Delta Gamma A1 A2 A3 A :
  Context Delta Gamma ||- C, {-A
    A /\ (A1 \/ A2 \/ A3) <->
    (A /\ A1) \/ (A /\ A2) \/ (A /\ A3)
  -}.
Proof.
  dsplit; dif.
  - by dsplitp; dswap; dorp;
    [dleft | dright; dorp; [dleft | dright] ];
    dsplit; dassumption.
  - by dorp; [| dorp]; dsplitp; dsplit; (try by dhead);
    [dleft | dright; dleft | dright; dright]; dassumption.
Qed.

Lemma DSOrDistribAnd4 C Delta Gamma A1 A2 A3 A4 A :
  Context Delta Gamma ||- C, {-A
    A /\ (A1 \/ A2 \/ A3 \/ A4) <->
    (A /\ A1) \/ (A /\ A2) \/ (A /\ A3) \/ (A /\ A4)
  -}.
Proof.
  dsplit; dif.
  - by dsplitp; dswap; dorp; [| dorp; [| dorp] ];
    [dleft | dright; dleft | dright; dright; dleft | dright; dright; dright];
    dsplit; dassumption.
  - by dsplit; dorp; [| dorp; [| dorp] | |]; (try by dsplitp);
    [dleft | dright; dorp; [dleft | dright; dorp; [dleft | dright] ] ];
    dsplitp; dassumption.
Qed.

Lemma DSExistsDistribOr2 C Delta A1 A2 :
  assertion_closed_in [:: 1] Delta A1 ->
  assertion_closed_in [:: 1] Delta A2 ->
  Context Delta [::] ||- C, {-A
    (exists: (A1 \/ A2)) <->
    (exists: A1) \/ (exists: A2)
   -}.
Proof.
  move=> Hc_A1 Hc_A2.
  dsplit; dif.
  - dexistsp x; dsimplfresh.
    + move/norP: Hf_x => [Hf_x_A1 Hf_x];
      move/norP: Hf_x => [Hf_x_A2 Hf_x];
      rewrite /context_rigids /= !mem_cat;
      by apply/norP; split; [| apply/norP; split].
    + admit.
    dorp; [dleft | dright]; dexists x.
  (* - by dorp; dexistsp z; dexists z; [dleft | dright]. *)
  - admit.
Admitted.

Lemma DSExistsDistribOr3 C Delta A1 A2 A3 :
  assertion_closed_in [:: 1] Delta A1 ->
  assertion_closed_in [:: 1] Delta A2 ->
  assertion_closed_in [:: 1] Delta A3 ->
  Context Delta [::] ||- C, {-A
    (exists: (A1 \/ A2 \/ A3)) <->
    ((exists: A1) \/ (exists: A2) \/ (exists: A3))
   -}.
Proof.
  move=> Hc_A1 Hc_A2 Hc_A3.
  dsplit; dif.
  (*
  - by dexistsp z; dorp;
    [| dorp]; [dleft | dright; [dleft | dright] ]; dexists z.
  - by dorp; [| dorp]; dexistsp z; dexists z.
  *)
  - admit.
  - admit.
Admitted.
