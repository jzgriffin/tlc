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

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Basic syntactic rules and axioms *)
Section derives.

  Variable C : component.

  Reserved Notation "Gamma |- A" (at level 70, no associativity).
  Inductive derives : context -> assertion -> Prop :=
  (* Evaluation *)
  | DAEvaluateP Gamma Ap Ap' Ac :
    [[A Ap]] = Success Ap' ->
    Ap' :: Gamma |- Ac ->
    Ap :: Gamma |- Ac
  | DAEvaluateP' Gamma Ap Ap' Ac :
    [[A Ap]] = Success Ap' ->
    Ap :: Gamma |- Ac ->
    Ap' :: Gamma |- Ac
  | DAEvaluateC Gamma Ac Ac' :
    [[A Ac]] = Success Ac' ->
    Gamma |- Ac' ->
    Gamma |- Ac
  | DAEvaluateC' Gamma Ac Ac' :
    [[A Ac]] = Success Ac' ->
    Gamma |- Ac ->
    Gamma |- Ac'
  (* Substitution *)
  | DASubstituteP Gamma Ap Ac :
    (Ap /A/ context_equivalences Gamma) :: Gamma |- Ac ->
    Ap :: Gamma |- Ac
  | DASubstituteC Gamma Ac :
    Gamma |- (Ac /A/ context_equivalences Gamma) ->
    Gamma |- Ac
  (* Implication rewriting *)
  | DARewriteIfP Gamma Arp Arc Ap Ac :
    Gamma |- {A: Arp -> Arc} ->
    (rewrite_assertion_pos Arp Arc Ap) :: Gamma |- Ac ->
    Ap :: Gamma |- Ac
  | DARewriteIfP' Gamma Arp Arc Ap Ac :
    Gamma |- {A: Arp -> Arc} ->
    Ap :: Gamma |- Ac ->
    (rewrite_assertion_pos Arp Arc Ap) :: Gamma |- Ac
  | DARewriteIfC Gamma Arp Arc Ac :
    Gamma |- {A: Arp -> Arc} ->
    Gamma |- (rewrite_assertion_pos Arp Arc Ac) ->
    Gamma |- Ac
  | DARewriteIfC' Gamma Arp Arc Ac :
    Gamma |- {A: Arp -> Arc} ->
    Gamma |- Ac ->
    Gamma |- (rewrite_assertion_pos Arp Arc Ac)
  (* Bicondition rewriting *)
  | DARewriteIffPL Gamma Arp Arc Ap Ac :
    Gamma |- {A: Arp <-> Arc} ->
    (rewrite_assertion_any Arp Arc Ap) :: Gamma |- Ac ->
    Ap :: Gamma |- Ac
  | DARewriteIffCL Gamma Arp Arc Ac :
    Gamma |- {A: Arp <-> Arc} ->
    Gamma |- (rewrite_assertion_any Arp Arc Ac) ->
    Gamma |- Ac
  | DARewriteIffPR Gamma Arp Arc Ap Ac :
    Gamma |- {A: Arp <-> Arc} ->
    (rewrite_assertion_any Arc Arp Ap) :: Gamma |- Ac ->
    Ap :: Gamma |- Ac
  | DARewriteIffCR Gamma Arp Arc Ac :
    Gamma |- {A: Arp <-> Arc} ->
    Gamma |- (rewrite_assertion_any Arc Arp Ac) ->
    Gamma |- Ac
  (* Implication rewriting *)
  | DARewriteEntailsP Gamma Arp Arc Ap Ac :
    Gamma |- {A: Arp =>> Arc} ->
    (rewrite_assertion_pos Arp Arc Ap) :: Gamma |- Ac ->
    Ap :: Gamma |- Ac
  | DARewriteEntailsP' Gamma Arp Arc Ap Ac :
    Gamma |- {A: Arp =>> Arc} ->
    Ap :: Gamma |- Ac ->
    (rewrite_assertion_pos Arp Arc Ap) :: Gamma |- Ac
  | DARewriteEntailsC Gamma Arp Arc Ac :
    Gamma |- {A: Arp =>> Arc} ->
    Gamma |- (rewrite_assertion_pos Arp Arc Ac) ->
    Gamma |- Ac
  | DARewriteEntailsC' Gamma Arp Arc Ac :
    Gamma |- {A: Arp =>> Arc} ->
    Gamma |- Ac ->
    Gamma |- (rewrite_assertion_pos Arp Arc Ac)
  (* Bicondition rewriting *)
  | DARewriteCongruentPL Gamma Arp Arc Ap Ac :
    Gamma |- {A: Arp <=> Arc} ->
    (rewrite_assertion_any Arp Arc Ap) :: Gamma |- Ac ->
    Ap :: Gamma |- Ac
  | DARewriteCongruentCL Gamma Arp Arc Ac :
    Gamma |- {A: Arp <=> Arc} ->
    Gamma |- (rewrite_assertion_any Arp Arc Ac) ->
    Gamma |- Ac
  | DARewriteCongruentPR Gamma Arp Arc Ap Ac :
    Gamma |- {A: Arp <=> Arc} ->
    (rewrite_assertion_any Arc Arp Ap) :: Gamma |- Ac ->
    Ap :: Gamma |- Ac
  | DARewriteCongruentCR Gamma Arp Arc Ac :
    Gamma |- {A: Arp <=> Arc} ->
    Gamma |- (rewrite_assertion_any Arc Arp Ac) ->
    Gamma |- Ac
  (* Predicates *)
  | DAPEqual Gamma tl tr :
    tl = tr ->
    Gamma |- {A: tl = tr}
  | DAPIn Gamma t ts ts' :
    lift_list ts = Success ts' ->
    t \in ts' ->
    Gamma |- {A: t \in ts}
  (* Constructors *)
  | DAInjectivePairP Gamma tll trl tlr trr Ac :
    {A: tll = tlr} :: {A: trl = trr} :: Gamma |- Ac ->
    {A: {t: (tll, trl)} = {t: (tlr, trr)}} :: Gamma |- Ac
  | DAInjectivePairC Gamma tll trl tlr trr :
    Gamma |- {A: tll = tlr} ->
    Gamma |- {A: trl = trr} ->
    Gamma |- {A: {t: (tll, trl)} = {t: (tlr, trr)}}
  (* Sequent logic *)
  | DSFalse Gamma A :
    AFalse :: Gamma |- A
  | DSAxiom Gamma A :
    A :: Gamma |- A
  | DSThin Gamma Ap Ac :
    Gamma |- Ac ->
    Ap :: Gamma |- Ac
  | DSContraction Gamma Ap A2 :
    Ap :: Ap :: Gamma |- A2 ->
    Ap :: Gamma |- A2
  | DSExchange Gamma Ap1 Ap2 Ac :
    Ap1 :: Ap2 :: Gamma |- Ac ->
    Ap2 :: Ap1 :: Gamma |- Ac
  | DSCut Gamma Ap Ac :
    Gamma |- Ap ->
    Ap :: Gamma |- Ac ->
    Gamma |- Ac
  | DSNotP Gamma Ap Ac :
    Gamma |- Ap ->
    {A: ~Ap} :: Gamma |- Ac
  | DSNotC Gamma Ac :
    Ac :: Gamma |- AFalse ->
    Gamma |- {A: ~Ac}
  | DSOrP Gamma Apl Apr Ac :
    Apl :: Gamma |- Ac ->
    Apr :: Gamma |- Ac ->
    {A: Apl \/ Apr} :: Gamma |- Ac
  | DSOrCL Gamma Acl Acr :
    Gamma |- Acl ->
    Gamma |- {A: Acl \/ Acr}
  | DSOrCR Gamma Acl Acr :
    Gamma |- Acr ->
    Gamma |- {A: Acl \/ Acr}
  | DSAndP Gamma Apl Apr Ac :
    Apl :: Apr :: Gamma |- Ac ->
    {A: Apl /\ Apr} :: Gamma |- Ac
  | DSAndC Gamma Acl Acr :
    Gamma |- Acl ->
    Gamma |- Acr ->
    Gamma |- {A: Acl /\ Acr}
  | DSIfP Gamma Apl Apr Ac :
    Gamma |- Apl ->
    Apr :: Gamma |- Ac ->
    {A: Apl -> Apr} :: Gamma |- Ac
  | DSIfC Gamma Acl Acr :
    Acl :: Gamma |- Acr ->
    Gamma |- {A: Acl -> Acr}
  | DSForAllP Gamma v t Ap Ac :
    instantiate_assertion [:: (v, t)] Ap :: Gamma |- Ac ->
    {A: forall: v, Ap} :: Gamma |- Ac
  | DSForAllC Gamma v t Ac :
    Gamma |- instantiate_assertion [:: (v, t)] Ac ->
    Gamma |- {A: forall: v, Ac}
  | DSExistsP Gamma v t Ap Ac :
    instantiate_assertion [:: (v, t)] Ap :: Gamma |- Ac ->
    {A: exists: v, Ap} :: Gamma |- Ac
  | DSExistsC Gamma v t Ac :
    Gamma |- instantiate_assertion [:: (v, t)] Ac ->
    Gamma |- {A: exists: v, Ac}
  (* Temporal logic future *)
  | DT1 Gamma A :
    Gamma |- {A: always A -> A}
  | DT2 Gamma A :
    Gamma |- {A: (next ~A) <=> ~next A}
  | DT3 Gamma Al Ar :
    Gamma |- {A: (next (Al -> Ar)) <=> (next Al -> next Ar)}
  | DT4 Gamma Al Ar :
    Gamma |- {A: (always (Al -> Ar)) =>> (always Al -> always Ar)}
  | DT5 Gamma A :
    Gamma |- {A: (always A) -> always next A}
  | DT6 Gamma A :
    Gamma |- {A: (A =>> next A) -> (A =>> always A)}
  | DT7 Gamma Al Ar :
    Gamma |- {A: (Al unless Ar) <=> (Ar \/ (Al /\ next (Al unless Ar)))}
  | DT8 Gamma Al Ar :
    Gamma |- {A: (always Al) =>> Al unless Ar}
  (* Temporal logic past *)
  | DT9 Gamma A :
    Gamma |- {A: previous A =>> previous^ A}
  | DT10 Gamma Al Ar :
    Gamma |- {A: previous^ (Al -> Ar) <=> (previous^ Al -> previous^ Ar)}
  | DT11 Gamma Al Ar :
    Gamma |- {A: alwaysp (Al -> Ar) =>> (alwaysp Al -> alwaysp Ar)}
  | DT12 Gamma A :
    Gamma |- {A: always A -> always previous^ A}
  | DT13 Gamma A :
    Gamma |- {A: (A =>> previous^ A) -> (A =>> alwaysp A)}
  | DT14 Gamma Al Ar :
    Gamma |- {A:
      (Al backto Ar) <=> (Ar \/ (Al /\ previous^ (Al backto Ar)))
    }
  | DT15 Gamma :
    Gamma |- previous^ AFalse
  (* Temporal logic mixed *)
  | DT16 Gamma A :
    Gamma |- {A: A =>> next previous A}
  | DT17 Gamma A :
    Gamma |- {A: A =>> previous^ next A}
  (* Temporal logic rules *)
  | DTGeneralization Gamma A :
    Gamma |- A ->
    Gamma |- {A: always A}
  | DT18 Gamma v A :
    Gamma |- {A: (forall: v, next A) <=> (next forall: v, A)}
  (* Program logic *)
  | DPNode Gamma :
    Gamma |- {A: always ("n" \in "Nodes")}
  | DPIR Gamma te :
    Gamma |- {A:
      when[]-> te =>>
      (("Fs'" $ "Fn", "Fors", "Fois") =
        request C $ "Fn" $ ("Fs" $ "Fn") $ te)
    }
  | DPII Gamma ti te :
    Gamma |- {A:
      when[ti]<- te =>>
      (("Fs'" $ "Fn", "Fors", "Fois") =
        indication C $ "Fn" $ ("Fs" $ "Fn") $ (ti, te))
    }
  | DPPe Gamma :
    Gamma |- {A:
      when[]~> PE =>>
      (("Fs'" $ "Fn", "Fors", "Fois") =
        periodic C $ "Fn" $ ("Fs" $ "Fn"))
    }
  | DPOR Gamma tn ti te :
    Gamma |- {A:
      when-on[tn] (when-self /\ (ti, te) \in "Fors") =>>
      eventually^ when-on[tn] when[ti]-> te
    }
  | DPOI Gamma tn te :
    Gamma |- {A:
      when-on[tn] (te \in "Fois" /\ when-self) =>>
      eventually^ when-on[tn] when[]<- te
    }
  | DPOR' Gamma tn ti te :
    Gamma |- {A:
      eventuallyp^ when-on[tn] when[ti]-> te =>>
      when-on[tn] ((ti, te) \in "Fors" /\ when-self)
    }
  | DPOI' Gamma tn te :
    Gamma |- {A:
      eventuallyp^ when-on[tn] when[]<- te =>>
      when-on[tn] (te \in "Fois" /\ when-self)
    }
  | DPInit Gamma :
    Gamma |- {A: self ("Fs" = fun: initialize C $ #0)}
  | DPPostPre Gamma ts :
    Gamma |- {A: self ("Fs'" = ts <=> next ("Fs" = ts))}
  | DPSEq Gamma tn :
    Gamma |- {A: "Fn" <> tn =>> "Fs'" $ tn = "Fs" $ tn}
  | DPASelf Gamma :
    Gamma |- {A: self always when-self}
  (* TODO: SInv *)
  | DPCSet Gamma tn :
    Gamma |- {A: correct tn <-> tn \in "Correct"}
  | DPAPer Gamma tn :
    Gamma |- {A:
      correct tn -> always eventually when-on[tn] when[]~> PE
    }
  | DPFLoss Gamma tn tn' tm ti :
    Gamma |- {A:
      correct tn' ->
      always^ eventually^ when-on[tn] when[ti]-> CFLSend $ tn' $ tm ->
      always^ eventually^ when-on[tn'] when[ti]<- CFLDeliver $ tn $ tm
    }
  | DPFDup Gamma tn tn' tm ti :
    Gamma |- {A:
      always eventually when-on[tn'] when[ti]<- CFLDeliver $ tn $ tm ->
      always eventually when-on[tn] when[ti]-> CFLSend $ tn' $ tm
    }
  | DPNForge Gamma tn tn' tm ti :
    Gamma |- {A:
      when-on[tn'] when[ti]<- CFLDeliver $ tn $ tm =>>
      eventuallyp when-on[tn] when[ti]-> CFLSend $ tn' $ tm
    }
  (* TODO: UniOR *)
  (* TODO: UniOI *)
  where "Gamma |- A" := (derives Gamma A).

End derives.

Notation "Gamma |- C , A" := (derives C Gamma A)
  (at level 70, no associativity).

Hint Constructors derives.

(* Extracts the assertion from a proof *)
Definition derives_assertion C Gamma A (H : Gamma |- C, A) := A.
