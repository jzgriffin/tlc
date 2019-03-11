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

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Basic syntactic rules and axioms *)
Section derives.

  Variable C : component.

  Reserved Notation "ctx |- A" (at level 70, no associativity).
  Inductive derives : context -> assertion -> Prop :=
  (* Evaluation *)
  | DAEvaluateP Delta Gamma Ap Ap' Ac :
    [[A Ap]] = Success Ap' ->
    Context Delta (Ap' :: Gamma) |- Ac ->
    Context Delta (Ap :: Gamma) |- Ac
  | DAEvaluateC ctx Ac Ac' :
    [[A Ac]] = Success Ac' ->
    ctx |- Ac' ->
    ctx |- Ac
  (* Substitution *)
  | DASubstituteP Delta Gamma Ap Ac :
    Context Delta (Ap /A/ context_equivalences Gamma :: Gamma) |- Ac ->
    Context Delta (Ap :: Gamma) |- Ac
  | DASubstituteC ctx Ac :
    ctx |- (Ac /A/ context_equivalences ctx) ->
    ctx |- Ac
  (* Implication rewriting *)
  | DARewriteIfP Delta Gamma Arp Arc Ap Ac :
    Context Delta Gamma |- {A: Arp -> Arc} ->
    Context Delta (rewrite_assertion_pos Arp Arc Ap :: Gamma) |- Ac ->
    Context Delta (Ap :: Gamma) |- Ac
  | DARewriteIfC ctx Arp Arc Ac :
    ctx |- {A: Arp -> Arc} ->
    ctx |- rewrite_assertion_pos Arp Arc Ac ->
    ctx |- Ac
  (* Bicondition rewriting *)
  | DARewriteIffPL Delta Gamma Arp Arc Ap Ac :
    Context Delta Gamma |- {A: Arp <-> Arc} ->
    Context Delta (rewrite_assertion_any Arp Arc Ap :: Gamma) |- Ac ->
    Context Delta (Ap :: Gamma) |- Ac
  | DARewriteIffCL ctx Arp Arc Ac :
    ctx |- {A: Arp <-> Arc} ->
    ctx |- rewrite_assertion_any Arp Arc Ac ->
    ctx |- Ac
  | DARewriteIffPR Delta Gamma Arp Arc Ap Ac :
    Context Delta Gamma |- {A: Arp <-> Arc} ->
    Context Delta (rewrite_assertion_any Arc Arp Ap :: Gamma) |- Ac ->
    Context Delta (Ap :: Gamma) |- Ac
  | DARewriteIffCR ctx Arp Arc Ac :
    ctx |- {A: Arp <-> Arc} ->
    ctx |- rewrite_assertion_any Arc Arp Ac ->
    ctx |- Ac
  (* Implication rewriting *)
  | DARewriteEntailsP Delta Gamma Arp Arc Ap Ac :
    Context Delta Gamma |- {A: Arp =>> Arc} ->
    Context Delta (rewrite_assertion_pos Arp Arc Ap :: Gamma) |- Ac ->
    Context Delta (Ap :: Gamma) |- Ac
  | DARewriteEntailsC ctx Arp Arc Ac :
    ctx |- {A: Arp =>> Arc} ->
    ctx |- rewrite_assertion_pos Arp Arc Ac ->
    ctx |- Ac
  (* Bicondition rewriting *)
  | DARewriteCongruentPL Delta Gamma Arp Arc Ap Ac :
    Context Delta Gamma |- {A: Arp <=> Arc} ->
    Context Delta (rewrite_assertion_any Arp Arc Ap :: Gamma) |- Ac ->
    Context Delta (Ap :: Gamma) |- Ac
  | DARewriteCongruentCL ctx Arp Arc Ac :
    ctx |- {A: Arp <=> Arc} ->
    ctx |- rewrite_assertion_any Arp Arc Ac ->
    ctx |- Ac
  | DARewriteCongruentPR Delta Gamma Arp Arc Ap Ac :
    Context Delta Gamma |- {A: Arp <=> Arc} ->
    Context Delta (rewrite_assertion_any Arc Arp Ap :: Gamma) |- Ac ->
    Context Delta (Ap :: Gamma) |- Ac
  | DARewriteCongruentCR ctx Arp Arc Ac :
    ctx |- {A: Arp <=> Arc} ->
    ctx |- rewrite_assertion_any Arc Arp Ac ->
    ctx |- Ac
  (* Predicates *)
  | DAPEqual ctx tl tr :
    tl = tr ->
    ctx |- {A: tl = tr}
  | DAPIn ctx t ts ts' :
    lift_list ts = Success ts' ->
    t \in ts' ->
    ctx |- {A: t \in ts}
  | DAPExtension ctx ts' ts'_l ts ts_l :
    lift_list ts' = Success ts'_l ->
    lift_list ts = Success ts_l ->
    extension ts'_l ts_l ->
    ctx |- {A: ts' <<< ts}
  (* Constructors *)
  | DAInjectivePairP Delta Gamma tll trl tlr trr Ac :
    Context Delta ({A: tll = tlr} :: {A: trl = trr} :: Gamma) |- Ac ->
    Context Delta ({A: (tll, trl) = (tlr, trr)} :: Gamma) |- Ac
  | DAInjectivePairC ctx tll trl tlr trr :
    ctx |- {A: tll = tlr} ->
    ctx |- {A: trl = trr} ->
    ctx |- {A: (tll, trl) = (tlr, trr)}
  (* Sequent logic *)
  | DSFalse Delta Gamma A :
    Context Delta (AFalse :: Gamma) |- A
  | DSAxiom Delta Gamma A :
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
    ctx |- {A: always ("n" \in "Nodes")}
  | DPIR ctx :
    ctx |- {A:
      forall: "e":
      when[]-> "e" =>>
      (("Fs'" $ "Fn", "Fors", "Fois") =
        request C $ "Fn" $ ("Fs" $ "Fn") $ "e")
    }
  | DPII ctx :
    ctx |- {A:
      forall: "i", "e":
      when["i"]<- "e" =>>
      (("Fs'" $ "Fn", "Fors", "Fois") =
        indication C $ "Fn" $ ("Fs" $ "Fn") $ ("i", "e"))
    }
  | DPPe ctx :
    ctx |- {A:
      when[]~> PE =>>
      (("Fs'" $ "Fn", "Fors", "Fois") =
        periodic C $ "Fn" $ ("Fs" $ "Fn"))
    }
  | DPOR ctx :
    ctx |- {A:
      forall: "n", "i", "e":
      when-on["n"] (when-self /\ ("i", "e") \in "Fors") =>>
      eventually^ when-on["n"] when["i"]-> "e"
    }
  | DPOI ctx :
    ctx |- {A:
      forall: "n", "e":
      when-on["n"] ("e" \in "Fois" /\ when-self) =>>
      eventually^ when-on["n"] when[]<- "e"
    }
  | DPOR' ctx :
    ctx |- {A:
      forall: "n", "i", "e":
      when-on["n"] when["i"]-> "e" =>>
      eventuallyp^ (when-on["n"] (("i", "e") \in "Fors") /\ when-self)
    }
  | DPOI' ctx :
    ctx |- {A:
      forall: "n", "e":
      when-on["n"] when[]<- "e" =>>
      eventuallyp^ (when-on["n"] ("e" \in "Fois") /\ when-self)
    }
  | DPInit ctx :
    ctx |- {A: self ("Fs" = fun: initialize C $ #0)}
  | DPPostPre ctx :
    ctx |- {A: forall: "s": self ("Fs'" = "s" <=> next ("Fs" = "s"))}
  | DPSEq ctx :
    ctx |- {A: forall: "n": "Fn" <> "n" =>> "Fs'" $ "n" = "Fs" $ "n"}
  | DPASelf ctx :
    ctx |- {A: self always when-self}
  | DPSInv ctx A :
    self_invariant A ->
    ctx |- {A: self A <-> restrict_assertion {A: when-self} A}
  | DPCSet ctx :
    ctx |- {A: forall: "n": correct "n" <-> "n" \in "Correct"}
  | DPAPer ctx :
    ctx |- {A:
      forall: "n":
      correct "n" -> always eventually when-on["n"] when[]~> PE
    }
  | DPFLoss ctx tn tn' tm ti :
    ctx |- {A:
      correct tn' ->
      always^ eventually^ when-on[tn] when[ti]-> CFLSend $ tn' $ tm ->
      always^ eventually^ when-on[tn'] when[ti]<- CFLDeliver $ tn $ tm
    }
  | DPFDup ctx tn tn' tm ti :
    ctx |- {A:
      always eventually when-on[tn'] when[ti]<- CFLDeliver $ tn $ tm ->
      always eventually when-on[tn] when[ti]-> CFLSend $ tn' $ tm
    }
  | DPNForge ctx tn tn' tm ti :
    ctx |- {A:
      when-on[tn'] when[ti]<- CFLDeliver $ tn $ tm =>>
      eventuallyp when-on[tn] when[ti]-> CFLSend $ tn' $ tm
    }
  (* TODO: UniOR *)
  (* TODO: UniOI *)
  where "ctx |- A" := (derives ctx A).

End derives.

Notation "ctx |- C , A" := (derives C ctx A)
  (at level 70, no associativity).

Hint Constructors derives.

(* Extracts the context from a proof *)
Definition derives_context C ctx A (H : ctx |- C, A) := ctx.

(* Extracts the assertion from a proof *)
Definition derives_assertion C ctx A (H : ctx |- C, A) := A.

(* Tactics *)
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

(* Sequent logic tactics *)
Tactic Notation "d_false" := apply DSFalse.
Tactic Notation "d_assumption" constr(n) :=
  do n apply DSThin; apply DSAxiom.
Tactic Notation "d_clear" := apply DSThin.
Tactic Notation "d_swap" := apply DSExchange.
Ltac d_have Ap :=
  match goal with
  | [ |- derives ?C (Context ?Delta ?Gamma) ?Ac ] =>
    apply (@DSCut C Delta Gamma Ap Ac)
  | _ => fail
  end.
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
