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
  by dnotc.
Qed.

Hint Resolve DSTrue : core.

(* Negation is the same as implication with a false conclusion *)
Lemma DSNotImpliesFalse C Delta Gamma A :
  Context Delta Gamma ||- C, {-A ~A <-> (A -> AFalse) -}.
Proof.
  dsplitc; difc.
  - by difc; dswap; dnotp.
  - by dnotc; dswap; dnotp; dsplitc; dnotc; [dnotp |].
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
  by dsplitc; difc; dsplitp; dsplitc; try by []; by dclear.
Qed.

(* Associativity of And *)
Lemma DSAndAssoc C Delta Gamma A1 A2 A3 :
  Context Delta Gamma ||- C, {-A
    (A1 /\ A2) /\ A3 <->
    A1 /\ (A2 /\ A3)
  -}.
Proof.
  dsplitc; difc.
  - by dsplitp; dsplitp; dsplitc; [| dsplitc]; dassumption.
  - by dsplitp; dswap; dsplitp; dsplitc; [dsplitc |]; dassumption.
Qed.

(* Elimination of And with True *)
Lemma DSAndElimTL C Delta Gamma A :
  Context Delta Gamma ||- C, {-A ATrue /\ A <-> A -}.
Proof.
  dsplitc; difc.
  - by dsplitp; dassumption.
  - by dsplitc; first by dnotc.
Qed.

Lemma DSAndElimTR C Delta Gamma A :
  Context Delta Gamma ||- C, {-A A /\ ATrue <-> A -}.
Proof.
  dsplitc; difc.
  - by dsplitp.
  - by dsplitc; last by dnotc.
Qed.

(* Elimination of And with False *)
Lemma DSAndElimFL C Delta Gamma A :
  Context Delta Gamma ||- C, {-A AFalse /\ A <-> AFalse -}.
Proof.
  dsplitc; difc.
  - by dsplitp.
  - by dsplitc.
Qed.

Lemma DSAndElimFR C Delta Gamma A :
  Context Delta Gamma ||- C, {-A A /\ AFalse <-> AFalse -}.
Proof.
  dsplitc; difc.
  - by dsplitp; dassumption.
  - by dsplitc.
Qed.

(* Commutativity of Or *)
Lemma DSOrComm C Delta Gamma Acl Acr :
  Context Delta Gamma ||- C, {-A (Acl \/ Acr) <-> (Acr \/ Acl) -}.
Proof.
  by dsplitc; difc; dorp; (try by dleft); (try by dright).
Qed.

(* Elimination of Or with True *)
Lemma DSOrElimTL C Delta Gamma A :
  Context Delta Gamma ||- C, {-A ATrue \/ A <-> ATrue -}.
Proof.
  by dsplitc; difc; [dorp | dleft]; dnotc.
Qed.

Lemma DSOrElimTR C Delta Gamma A :
  Context Delta Gamma ||- C, {-A A \/ ATrue <-> ATrue -}.
Proof.
  by dsplitc; difc; [dorp | dright]; dnotc.
Qed.

(* Elimination of Or with False *)
Lemma DSOrElimFL C Delta Gamma A :
  Context Delta Gamma ||- C, {-A AFalse \/ A <-> A -}.
Proof.
  by dsplitc; difc; [dorp | dright].
Qed.

Lemma DSOrElimFR C Delta Gamma A :
  Context Delta Gamma ||- C, {-A A \/ AFalse <-> A -}.
Proof.
  by dsplitc; difc; [dorp | dleft].
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
  dsplitc.
  - by difc; difc; dsplitp; dxchg0 2; difp; [| difp]; dassumption.
  - by difc; difc; difc; dxchg0 2; difp; [dsplitc |]; dassumption.
Qed.

Lemma DSIfAndDropL C Delta Gamma A1 A2 :
  Context Delta Gamma ||- C, {-A
    A1 /\ A2 -> A2
   -}.
Proof.
  by difc; dsplitp; dswap.
Qed.

Lemma DSIfAndDropR C Delta Gamma A1 A2 :
  Context Delta Gamma ||- C, {-A
    A1 /\ A2 -> A1
   -}.
Proof.
  by difc; dsplitp.
Qed.

Lemma DSIfMergeAnd C Delta Gamma H A1 A2 :
  Context Delta Gamma ||- C, {-A
    (H -> A1) /\ (H -> A2) ->
    (H -> A1 /\ A2)
   -}.
Proof.
  difc; dsplitp; difc; dsplitc.
  - dswap; difp; by [].
  - dswap; dclear; dswap; difp; by [].
Qed.

Lemma DSIfAndSplit C Delta Gamma H A1 A2 :
  Context Delta Gamma ||- C, {-A
    ((H -> A1) /\ (H -> A2)) <->
    (H -> (A1 /\ A2))
  -}.
Proof.
  dsplitc; difc.
  - dsplitp; difc; dsplitc.
    + by dswap; difp; first by dhead.
    + by dswap; dclear; dswap; difp; first by dhead.
  - dsplitc; difc; dswap; (difp; first by dhead); dsplitp.
    + by dhead.
    + by dswap.
Qed.

Lemma DSIfAndIntro C Delta Gamma H1 H2 A :
  Context Delta Gamma ||- C, {-A
    (H1 /\ H2 -> A) <->
    (H1 /\ H2 -> H1 /\ A)
  -}.
Proof.
  dsplitc; difc; difc.
  - by dsplitc; [dsplitp | dswap; difp].
  - by dswap; difp; [| dsplitp]; dassumption.
Qed.

Lemma DSIfAndElim C Delta Gamma H A1 A2 :
  Context Delta Gamma ||- C, {-A
    (H -> (A1 /\ A2)) ->
    (H -> A1)
  -}.
Proof.
  by difc; difc; dswap; difp; [| dsplitp].
Qed.

Lemma DSOrDistributesAnd C Delta Gamma Al Ar A :
  Context Delta Gamma ||- C, {-A A /\ (Al \/ Ar) <-> (A /\ Al) \/ (A /\ Ar) -}.
Proof.
  dsplitc; difc.
  - dsplitp; dswap; dorp.
    + by dleft; dsplitc; [dclear; dhead | dhead].
    + by dright; dsplitc; [dclear; dhead | dhead].
  - dsplitc.
    + by dorp; dsplitp; dhead.
    + by dorp; dsplitp; dclear; [dleft | dright].
Qed.

Lemma DSOrDistributesAnd3 C Delta Gamma A1 A2 A3 A :
  Context Delta Gamma ||- C, {-A
    A /\ (A1 \/ A2 \/ A3) <->
    (A /\ A1) \/ (A /\ A2) \/ (A /\ A3)
   -}.
Proof.
  dsplitc. difc.
  dsplitp. dswap. dorp.
  dleft. dsplitc. dswap; first by dhead. dhead.
  dright. dorp. dleft. dsplitc. dswap; first by dhead. dhead.
  dright. dsplitc. dswap; first by dhead. dhead.

  difc. dorp. dsplitc. dsplitp; first by dhead.
  dleft. dsplitp. dswap. dhead.
  dorp. dsplitc. dsplitp. dhead.
  dright. dleft. dsplitp; dswap. dhead.
  dsplitc. dsplitp. dhead.
  dright. dright. dsplitp; dswap. dhead.
Qed.

Lemma DSOrDistributesAnd4 C Delta Gamma A1 A2 A3 A4 A :
  Context Delta Gamma ||- C, {-A
    A /\ (A1 \/ A2 \/ A3 \/ A4) <->
    (A /\ A1) \/ (A /\ A2) \/ (A /\ A3) \/ (A /\ A4)
   -}.
Proof.
  dsplitc; difc.
  - dsplitp; dswap.
    dorp; first by dleft; dsplitc; [dclear; dhead | dhead].
    dorp; first by dright; dleft; dsplitc; [dclear; dhead | dhead].
    dorp; first by dright; dright; dleft; dsplitc; [dclear; dhead | dhead].
    dright; dright; dright; dsplitc; [dclear; dhead | dhead].
  - dsplitc; dorp.
    + by dsplitp.
    + by dorp; [dsplitp | dorp; dsplitp].
    + by dsplitp; dleft; by dswap.
    + dorp; [| dorp]; dsplitp; dswap; dright; [by dleft | dright | dright].
      * by dleft.
      * by dright.
Qed.

(*
Lemma DSExistsDistributesOr C Delta A1 A2 :
  is_assertion_closed 1 Delta A1 ->
  is_assertion_closed 1 Delta A2 ->
  Context Delta [::] ||- C, {-A
    (exists: (A1 \/ A2)) <->
    (exists: A1) \/ (exists: A2)
   -}.
Proof.
  move => HA1_c HA2_c.
  dsplitc; difc.
  - by dexistsp z Hf_z; dorp; [dleft | dright]; dexistsc z.
  - by dorp; dexistsp z Hf_z; dexistsc z; [dleft | dright].
Qed.

Lemma DSExistsDistributesOr3 C Delta A1 A2 A3 :
  is_assertion_closed 1 Delta A1 ->
  is_assertion_closed 1 Delta A2 ->
  is_assertion_closed 1 Delta A3 ->
  Context Delta [::] ||- C, {-A
    (exists: (A1 \/ A2 \/ A3)) <->
    ((exists: A1) \/ (exists: A2) \/ (exists: A3))
   -}.
Proof.
  move => HA1_c HA2_c HA3_c.
  dsplitc; difc.
  - dexistsp z Hf_z; dorp; [| dorp].
    + by dleft; dexistsc z.
    + by dright; dleft; dexistsc z.
    + by dright; dright; dexistsc z.
  - dorp; [| dorp]; dexistsp z Hf_z; dexistsc z.
    + by dleft.
    + by dright; dleft.
    + by dright; dright.
Qed.
*)
