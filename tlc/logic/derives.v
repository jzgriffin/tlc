(* TLC in Coq
 *
 * Module: tlc.logic.derives
 * Purpose: Contains the axioms for the syntactic proof system.
 *)

Require Import mathcomp.ssreflect.eqtype.
Require Import mathcomp.ssreflect.seq.
Require Import mathcomp.ssreflect.ssrbool.
Require Import mathcomp.ssreflect.ssreflect.
Require Import tlc.component.component.
Require Import tlc.logic.context.
Require Import tlc.operation.orientation.
Require Import tlc.operation.periodic_event.
Require Import tlc.semantics.all_semantics.
Require Import tlc.syntax.all_syntax.
Require Import tlc.utility.result.
Require Import tlc.utility.seq.
Require Import tlc.utility.set.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Basic syntactic rules and axioms *)
Section derives.

  Variable C : component.

  (* Meaning: Assuming ctx for component C, A is true. *)
  Reserved Notation "ctx |- A" (at level 70, no associativity).

  (* These rules and axioms use the following naming convention:
   * - Every constructor begins with D, followed by one of:
   *    - A for rules/axioms specific to this implementation
   *    - AP for rules/axioms specific to this implementation's predicates
   *    - S for rules/axioms from sequent logic
   *    - T for rules/axioms from temporal logic
   *    - P for rules/axioms from the program logic
   * - Constructors that end with P operate on the premises
   * - Constructors that end with C operate on the conclusion
   * - Sequent logic rules/axioms are named for the forms they operate on
   * - Temporal logic rules/axioms are named sequentially as in the paper
   * - Program logic rules/axioms are named as in the paper
   *)
  Inductive derives : context -> assertion -> Prop :=
  (* Evaluation rules *)
  | DAEvaluateP Delta Gamma Ap Ap' Ac :
    (* Replaces the head premise with its evaluation *)
    [[A Ap]] = Success Ap' ->
    Context Delta (Ap' :: Gamma) |- Ac ->
    Context Delta (Ap :: Gamma) |- Ac
  | DAEvaluateC ctx Ac Ac' :
    (* Replaces the conclusion with its evaluation *)
    [[A Ac]] = Success Ac' ->
    ctx |- Ac' ->
    ctx |- Ac
  (* Substitution *)
  | DASubstituteP Delta Gamma Ap Ac :
    (* Substitutes equivalences from the tail premises within the head *)
    Context Delta (Ap /A/ context_equivalences Gamma :: Gamma) |- Ac ->
    Context Delta (Ap :: Gamma) |- Ac
  | DASubstituteC ctx Ac :
    (* Substitutes equivalences from the premises within the conclusion *)
    ctx |- (Ac /A/ context_equivalences ctx) ->
    ctx |- Ac
  (* Implication rewriting *)
  | DARewriteIfP Delta Gamma Arp Arc Ap Ac :
    (* Rewrites an implication within the head premise *)
    Context Delta Gamma |- {A: Arp -> Arc} ->
    Context Delta (rewrite_assertion_pos Arp Arc Ap :: Gamma) |- Ac ->
    Context Delta (Ap :: Gamma) |- Ac
  | DARewriteIfC ctx Arp Arc Ac :
    (* Rewrites an implication within the conclusion *)
    ctx |- {A: Arp -> Arc} ->
    ctx |- rewrite_assertion_pos Arp Arc Ac ->
    ctx |- Ac
  (* Bicondition rewriting *)
  | DARewriteIffPL Delta Gamma Arp Arc Ap Ac :
    (* Rewrites a biconditional within the head premise, from left to right *)
    Context Delta Gamma |- {A: Arp <-> Arc} ->
    Context Delta (rewrite_assertion_any Arp Arc Ap :: Gamma) |- Ac ->
    Context Delta (Ap :: Gamma) |- Ac
  | DARewriteIffCL ctx Arp Arc Ac :
    (* Rewrites a binconditional within the conclusion, from left to right *)
    ctx |- {A: Arp <-> Arc} ->
    ctx |- rewrite_assertion_any Arp Arc Ac ->
    ctx |- Ac
  | DARewriteIffPR Delta Gamma Arp Arc Ap Ac :
    (* Rewrites a biconditional within the head premise, from right to left *)
    Context Delta Gamma |- {A: Arp <-> Arc} ->
    Context Delta (rewrite_assertion_any Arc Arp Ap :: Gamma) |- Ac ->
    Context Delta (Ap :: Gamma) |- Ac
  | DARewriteIffCR ctx Arp Arc Ac :
    (* Rewrites a binconditional within the conclusion, from right to left *)
    ctx |- {A: Arp <-> Arc} ->
    ctx |- rewrite_assertion_any Arc Arp Ac ->
    ctx |- Ac
  (* Implication rewriting *)
  | DARewriteEntailsP Delta Gamma Arp Arc Ap Ac :
    (* Rewrites a strong implication within the head premise *)
    Context Delta Gamma |- {A: Arp =>> Arc} ->
    Context Delta (rewrite_assertion_pos Arp Arc Ap :: Gamma) |- Ac ->
    Context Delta (Ap :: Gamma) |- Ac
  | DARewriteEntailsC ctx Arp Arc Ac :
    (* Rewrites a strong implication within the conclusion *)
    ctx |- {A: Arp =>> Arc} ->
    ctx |- rewrite_assertion_pos Arp Arc Ac ->
    ctx |- Ac
  (* Bicondition rewriting *)
  | DARewriteCongruentPL Delta Gamma Arp Arc Ap Ac :
    (* Rewrites a congruence within the head premise, from left to right *)
    Context Delta Gamma |- {A: Arp <=> Arc} ->
    Context Delta (rewrite_assertion_any Arp Arc Ap :: Gamma) |- Ac ->
    Context Delta (Ap :: Gamma) |- Ac
  | DARewriteCongruentCL ctx Arp Arc Ac :
    (* Rewrites a congruence within the conclusion, from left to right *)
    ctx |- {A: Arp <=> Arc} ->
    ctx |- rewrite_assertion_any Arp Arc Ac ->
    ctx |- Ac
  | DARewriteCongruentPR Delta Gamma Arp Arc Ap Ac :
    (* Rewrites a congruence within the head premise, from right to left *)
    Context Delta Gamma |- {A: Arp <=> Arc} ->
    Context Delta (rewrite_assertion_any Arc Arp Ap :: Gamma) |- Ac ->
    Context Delta (Ap :: Gamma) |- Ac
  | DARewriteCongruentCR ctx Arp Arc Ac :
    (* Rewrites a congruence within the conclusion, from right to left *)
    ctx |- {A: Arp <=> Arc} ->
    ctx |- rewrite_assertion_any Arc Arp Ac ->
    ctx |- Ac
  (* Predicates *)
  | DAPEqual ctx tl tr :
    (* Proves the equality of two terms *)
    tl = tr ->
    ctx |- {A: tl = tr}
  | DAPIn ctx t ts ts' :
    (* Proves that t is a member of list ts *)
    lift_list ts = Success ts' ->
    t \in ts' ->
    ctx |- {A: t \in ts}
  | DAPExtension ctx ts' ts'_l ts ts_l :
    (* Proves that ts' is an extension of ts *)
    lift_list ts' = Success ts'_l ->
    lift_list ts = Success ts_l ->
    extension ts'_l ts_l ->
    ctx |- {A: ts' <<< ts}
  (* Destructing *)
  | DADestructP Delta Gamma P ta cs Ac :
    Context Delta (destruct_matchp P ta cs :: Gamma) |- Ac ->
    Context Delta (P (TMatch ta cs) :: Gamma) |- Ac
  | DADestructC ctx P ta cs :
    ctx |- destruct_matchc P ta cs ->
    ctx |- P (TMatch ta cs)
  | DADestructPair ctx tll trl tlr trr :
    (* Proves the injective equality of two pairs *)
    ctx |- {A: (tll = tlr /\ trl = trr) <-> ((tll, trl) = (tlr, trr))}
  (* Variable context *)
  | DAExchangeV v1 v2 Delta Gamma Ac :
    Context (v1 :: v2 :: Delta) Gamma |- Ac ->
    Context (v2 :: v1 :: Delta) Gamma |- Ac
  | DAThinV v Delta Gamma Ac :
    v \in Delta ->
    v \notin big_union [seq assertion_free A | A <- Gamma] ->
    v \notin assertion_free Ac ->
    Context (rem v Delta) Gamma |- Ac ->
    Context Delta Gamma |- Ac
  (* Sequent logic *)
  | DSFalse Delta Gamma A :
    (* Proves that any assertion is true when false is assumed *)
    Context Delta (AFalse :: Gamma) |- A
  | DSAxiom Delta Gamma A :
    (* Proves that any assertion is true when it is assumed *)
    Context Delta (A :: Gamma) |- A
  | DSThin Delta Gamma Ap Ac :
    Context Delta Gamma |- Ac ->
    Context Delta (Ap :: Gamma) |- Ac
  | DSContraction Delta Gamma Ap A2 :
    Context Delta (Ap :: Ap :: Gamma) |- A2 ->
    Context Delta (Ap :: Gamma) |- A2
  | DSExchange Delta Gamma Ap1 Ap2 Ac :
    Context Delta (Ap1 :: Ap2 :: Gamma) |- Ac ->
    Context Delta (Ap2 :: Ap1 :: Gamma) |- Ac
  | DSCut Delta Gamma Ap Ac :
    Context Delta Gamma |- Ap ->
    Context Delta (Ap :: Gamma) |- Ac ->
    Context Delta Gamma |- Ac
  | DSNotP Delta Gamma Ap Ac :
    Context Delta Gamma |- Ap ->
    Context Delta ({A: ~Ap} :: Gamma) |- Ac
  | DSNotC Delta Gamma Ac :
    Context Delta (Ac :: Gamma) |- AFalse ->
    Context Delta Gamma |- {A: ~Ac}
  | DSOrP Delta Gamma Apl Apr Ac :
    Context Delta (Apl :: Gamma) |- Ac ->
    Context Delta (Apr :: Gamma) |- Ac ->
    Context Delta ({A: Apl \/ Apr} :: Gamma) |- Ac
  | DSOrCL ctx Acl Acr :
    ctx |- Acl ->
    ctx |- {A: Acl \/ Acr}
  | DSOrCR ctx Acl Acr :
    ctx |- Acr ->
    ctx |- {A: Acl \/ Acr}
  | DSAndP Delta Gamma Apl Apr Ac :
    Context Delta (Apl :: Apr :: Gamma) |- Ac ->
    Context Delta ({A: Apl /\ Apr} :: Gamma) |- Ac
  | DSAndC ctx Acl Acr :
    ctx |- Acl ->
    ctx |- Acr ->
    ctx |- {A: Acl /\ Acr}
  | DSIfP Delta Gamma App Apc Ac :
    Context Delta Gamma |- App ->
    Context Delta (Apc :: Gamma) |- Ac ->
    Context Delta ({A: App -> Apc} :: Gamma) |- Ac
  | DSIfC Delta Gamma Acp Acc :
    Context Delta (Acp :: Gamma) |- Acc ->
    Context Delta Gamma |- {A: Acp -> Acc}
  | DSForAllP Delta Gamma v t Ap Ac :
    Context Delta (instantiate_assertion [:: (v, t)] Ap :: Gamma) |- Ac ->
    Context Delta ({A: forall: v: Ap} :: Gamma) |- Ac
  | DSForAllC Delta Gamma v v' Ac :
    Context (v' :: Delta) Gamma |-
      instantiate_assertion [:: (v, TVariable v')] Ac ->
    Context Delta Gamma |- {A: forall: v: Ac}
  | DSExistsP Delta Gamma v v' Ap Ac :
    Context (v' :: Delta)
      (instantiate_assertion [:: (v, TVariable v')] Ap :: Gamma) |- Ac ->
    Context Delta ({A: exists: v: Ap} :: Gamma) |- Ac
  | DSExistsC ctx v t Ac :
    ctx |- instantiate_assertion [:: (v, t)] Ac ->
    ctx |- {A: exists: v: Ac}
  (* Temporal logic future *)
  | DT1 ctx A :
    ctx |- {A: always A -> A}
  | DT2 ctx A :
    ctx |- {A: (next ~A) <=> ~next A}
  | DT3 ctx Al Ar :
    ctx |- {A: (next (Al -> Ar)) <=> (next Al -> next Ar)}
  | DT4 ctx Al Ar :
    ctx |- {A: (always (Al -> Ar)) =>> (always Al -> always Ar)}
  | DT5 ctx A :
    ctx |- {A: (always A) -> always next A}
  | DT6 ctx A :
    ctx |- {A: (A =>> next A) -> (A =>> always A)}
  (* Temporal logic past *)
  | DT9 ctx A :
    ctx |- {A: previous A =>> previous^ A}
  | DT10 ctx Al Ar :
    ctx |- {A: previous^ (Al -> Ar) <=> (previous^ Al -> previous^ Ar)}
  | DT11 ctx Al Ar :
    ctx |- {A: alwaysp (Al -> Ar) =>> (alwaysp Al -> alwaysp Ar)}
  | DT12 ctx A :
    ctx |- {A: always A -> always previous^ A}
  | DT13 ctx A :
    ctx |- {A: (A =>> previous^ A) -> (A =>> alwaysp A)}
  | DT15 ctx :
    ctx |- previous^ AFalse
  (* Temporal logic mixed *)
  | DT16 ctx A :
    ctx |- {A: A =>> next previous A}
  | DT17 ctx A :
    ctx |- {A: A =>> previous^ next A}
  (* Temporal logic rules *)
  | DTGeneralization ctx A :
    ctx |- A ->
    ctx |- {A: always A}
  | DT18 ctx v A :
    ctx |- {A: (forall: v: next A) <=> (next forall: v: A)}
  (* Program logic *)
  | DPNode ctx :
    ctx |- {A:
      forall: "?n":
      always ("?n" \in "Nodes")
    }
  | DPIR ctx :
    ctx |- {A:
      forall: "?e":
      event []-> "?e" =>>
      ("Fs'" $ "Fn", "Fors", "Fois") =
        request C $ "Fn" $ ("Fs" $ "Fn") $ "?e"
    }
  | DPII ctx :
    ctx |- {A:
      forall: "?i", "?e":
      event ["?i"]<- "?e" =>>
      ("Fs'" $ "Fn", "Fors", "Fois") =
        indication C $ "Fn" $ ("Fs" $ "Fn") $ ("?i", "?e")
    }
  | DPPe ctx :
    ctx |- {A:
      event []~> PE =>>
      ("Fs'" $ "Fn", "Fors", "Fois") =
        periodic C $ "Fn" $ ("Fs" $ "Fn")
    }
  | DPOR ctx :
    ctx |- {A:
      forall: "?n", "?i", "?e":
      on "?n", (self-event /\ ("?i", "?e") \in "Fors") =>>
      eventually^ on "?n", event ["?i"]-> "?e"
    }
  | DPOI ctx :
    ctx |- {A:
      forall: "?n", "?e":
      on "?n", (self-event /\ "?e" \in "Fois") =>>
      eventually^ on "?n", event []<- "?e"
    }
  | DPOR' ctx :
    ctx |- {A:
      forall: "?n", "?i", "?e":
      on "?n", event ["?i"]-> "?e" =>>
      eventuallyp^ (self-event /\ on "?n", (("?i", "?e") \in "Fors"))
    }
  | DPOI' ctx :
    ctx |- {A:
      forall: "?n", "?e":
      on "?n", event []<- "?e" =>>
      eventuallyp^ (self-event /\ on "?n", ("?e" \in "Fois"))
    }
  | DPInit ctx :
    ctx |- {A: self ("Fs" = fun: initialize C $ #(0, 0))}
  | DPPostPre ctx :
    ctx |- {A: forall: "?s": self ("Fs'" = "?s" <=> next ("Fs" = "?s"))}
  | DPSEq ctx :
    ctx |- {A: forall: "?n": "Fn" <> "?n" =>> "Fs'" $ "?n" = "Fs" $ "?n"}
  | DPASelf ctx :
    ctx |- {A: self always self-event}
  | DPSInv ctx A :
    self_invariant A ->
    ctx |- {A: self A <-> restrict_assertion {A: self-event} A}
  | DPCSet ctx :
    ctx |- {A: forall: "?n": correct "?n" <-> "?n" \in "Correct"}
  | DPAPer ctx :
    ctx |- {A:
      forall: "?n":
      correct "?n" -> always eventually on "?n", event []~> PE
    }
  | DPFLoss ctx :
    ctx |- {A:
      forall: "?n", "?n'", "?m", "?i":
      correct "?n'" ->
      always^ eventually^ on "?n", event ["?i"]-> CFLSend $ "?n'" $ "?m" ->
      always^ eventually^ on "?n'", event ["?i"]<- CFLDeliver $ "?n" $ "?m"
    }
  | DPFDup ctx :
    ctx |- {A:
      forall: "?n", "?n'", "?m", "?i":
      always eventually on "?n'", event ["?i"]<- CFLDeliver $ "?n" $ "?m" ->
      always eventually on "?n", event ["?i"]-> CFLSend $ "?n'" $ "?m"
    }
  | DPNForge ctx :
    ctx |- {A:
      forall: "?n", "?n'", "?m", "?i":
      on "?n'", event ["?i"]<- CFLDeliver $ "?n" $ "?m" =>>
      eventuallyp on "?n", event ["?i"]-> CFLSend $ "?n'" $ "?m"
    }
  (* TODO: UniOR *)
  (* TODO: UniOI *)
  where "ctx |- A" := (derives ctx A).

End derives.

Notation "ctx |- C , A" := (derives C ctx A)
  (at level 70, no associativity).

Hint Constructors derives.

(* Extracts the context from a proof term *)
Definition derives_context C ctx A (H : ctx |- C, A) := ctx.

(* Extracts the assertion from a proof term *)
Definition derives_assertion C ctx A (H : ctx |- C, A) := A.

(* Tactics
 * Some of these tactics are named for their Coq equivalents.  For example,
 * d_clear uses the DSThin axiom but operates similarly to clear.
 *)

(* Implementation-specific *)
Tactic Notation "d_evalp" :=
  eapply DAEvaluateP; first by [].
Tactic Notation "d_evalc" :=
  eapply DAEvaluateC; first by [].
Tactic Notation "d_eval" :=
  d_evalp; d_evalc.
Tactic Notation "d_substp" :=
  apply DASubstituteP; rewrite /=.
Tactic Notation "d_substc" :=
  apply DASubstituteC; rewrite /=.
Tactic Notation "d_subst" :=
  d_substp; d_substc.
Tactic Notation "d_destructp" constr(Pp) :=
  eapply DADestructP with (P := Pp);
  rewrite /destruct_matchp /=.
Tactic Notation "d_destructc" constr(Pc) :=
  eapply DADestructC with (P := Pc);
  rewrite /destruct_matchc /=.
Tactic Notation "d_destructpairp"
  constr(tll) constr(trl) constr(tlr) constr(trr) :=
  eapply DARewriteIffPR; first by eapply DSCut;
    first by apply (DADestructPair _ _ tll trl tlr trr);
  rewrite_assertion_any.
Tactic Notation "d_destructtuplep"
  constr(t1l) constr(t2l) constr(t3l) constr(t1r) constr(t2r) constr(t3r) :=
  d_destructpairp {t: (t1l, t2l)} t3l {t: (t1r, t2r)} t3r;
  d_destructpairp t1l t2l t1r t2r;
  rewrite_assertion_any.
Tactic Notation "d_swapv" := apply DAExchangeV.
Tactic Notation "d_clearv" constr(x) :=
  eapply DAThinV with (v := x); [ by [] | by [] | by [] | ].

(* Sequent logic tactics *)
Tactic Notation "d_false" := apply DSFalse.
Tactic Notation "d_head" := apply DSAxiom.
Tactic Notation "d_clear" := apply DSThin.
Tactic Notation "d_swap" := apply DSExchange.
Ltac d_have Ap :=
  match goal with
  | [ |- derives ?C (Context ?Delta ?Gamma) ?Ac ] =>
    apply (@DSCut C Delta Gamma Ap Ac)
  | _ => fail
  end.
Ltac d_use L :=
  eapply DSCut; first by apply L.
Tactic Notation "d_notp" := apply DSNotP.
Tactic Notation "d_notc" := apply DSNotC.
Tactic Notation "d_orp" := apply DSOrP.
Tactic Notation "d_left" := apply DSOrCL.
Tactic Notation "d_right" := apply DSOrCR.
Tactic Notation "d_splitp" := apply DSAndP.
Tactic Notation "d_splitc" := apply DSAndC.
Tactic Notation "d_ifp" := apply DSIfP.
Tactic Notation "d_ifc" := apply DSIfC.
Tactic Notation "d_forallp" constr(x) :=
  apply DSForAllP with (t := x);
  rewrite /instantiate_assertion /=.
Tactic Notation "d_forallc" constr(x) :=
  apply DSForAllC with (v' := x);
  rewrite /instantiate_assertion /=.
Tactic Notation "d_existsp" constr(x) :=
  apply DSExistsP with (v' := x);
  rewrite /instantiate_assertion /=.
Tactic Notation "d_existsc" constr(x) :=
  apply DSExistsC with (t := x);
  rewrite /instantiate_assertion /=.
