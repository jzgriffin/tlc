Require Import mathcomp.ssreflect.eqtype.
Require Import mathcomp.ssreflect.seq.
Require Import mathcomp.ssreflect.ssrbool.
Require Import mathcomp.ssreflect.ssreflect.
Require Import tlc.component.component.
Require Import tlc.semantics.all_semantics.
Require Import tlc.syntax.all_syntax.
Require Import tlc.logic.context.
Require Import tlc.utility.result.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Basic syntactic rules and axioms *)
Reserved Notation "C |- c , A" (at level 70, no associativity).
Inductive derives (c : component) : context -> assertion -> Prop :=
(* Assertion logic *)
| DATrue C :
  C |- c, ATrue
| DAHypothesis C p p' A :
  [[p p[p/context_environment C] ]] = Success p' ->
  p' :: C |- c, A ->
  APredicate p :: C |- c, A
| DAConclusion C p p' :
  [[p p[p/context_environment C] ]] = Success p' ->
  C |- c, p' ->
  C |- c, APredicate p
(* Sequent logic *)
| DSAxiom C A :
  A :: C |- c, A
| DSThin C A1 A2 :
  C |- c, A2 ->
  A1 :: C |- c, A2
| DSContraction C A1 A2 :
  A1 :: A1 :: C |- c, A2 ->
  A1 :: C |- c, A2
| DSExchange C A1 A2 A3 :
  A1 :: A2 :: C |- c, A3 ->
  A2 :: A1 :: C |- c, A3
| DSCut C A1 A2 :
  C |- c, A1 ->
  A1 :: C |- c, A2 ->
  C |- c, A2
| DSNotL C A1 A2 :
  C |- c, A1 ->
  {A: ~A1} :: C |- c, A2
| DSNotR C A :
  A :: C |- c, AFalse ->
  C |- c, {A: ~A}
| DSOrL C A1 A2 A3 :
  A1 :: C |- c, A3 ->
  A2 :: C |- c, A3 ->
  {A: A1 \/ A2} :: C |- c, A3
| DSOrRL C A1 A2 :
  C |- c, A1 ->
  C |- c, {A: A1 \/ A2}
| DSOrRR C A1 A2 :
  C |- c, A2 ->
  C |- c, {A: A1 \/ A2}
| DSAndL C A1 A2 A3 :
  A1 :: A2 :: C |- c, A3 ->
  {A: A1 /\ A2} :: C |- c, A3
| DSAndR C A1 A2 :
  C |- c, A1 ->
  C |- c, A2 ->
  C |- c, {A: A1 /\ A2}
| DSIfL C A1 A2 A3 :
  C |- c, A1 ->
  A2 :: C |- c, A3 ->
  {A: A1 -> A2} :: C |- c, A3
| DSIfR C A1 A2 :
  A1 :: C |- c, A2 ->
  C |- c, {A: A1 -> A2}
| DSForAllL C v t A1 A2 :
  A1[A/ [:: (v, t)] ] :: C |- c, A2 ->
  {A: forall: v, A1} :: C |- c, A2
| DSForAllR C v t A :
  C |- c, A[A/ [:: (v, t)] ] ->
  C |- c, {A: forall: v, A}
| DSExistsL C v t A1 A2 :
  A1[A/ [:: (v, t)] ] :: C |- c, A2 ->
  {A: exists: v, A1} :: C |- c, A2
| DSExistsR C v t A :
  C |- c, A[A/ [:: (v, t)] ] ->
  C |- c, {A: exists: v, A}
(* Temporal logic future *)
| DT1 C A :
  C |- c, {A: always A -> A}
| DT2 C A :
  C |- c, {A: (next ~A) <=> ~next A}
| DT3 C Al Ar :
  C |- c, {A: (next (Al -> Ar)) <=> (next Al -> next Ar)}
| DT4 C Al Ar :
  C |- c, {A: (always (Al -> Ar)) =>> (always Al -> always Ar)}
| DT5 C A :
  C |- c, {A: (always A) -> always next A}
| DT6 C A :
  C |- c, {A: (A =>> next A) -> (A =>> always A)}
| DT7 C Al Ar :
  C |- c, {A: (Al unless Ar) <=> (Ar \/ (Al /\ next (Al unless Ar)))}
| DT8 C Al Ar :
  C |- c, {A: (always Al) =>> Al unless Ar}
(* Temporal logic past *)
| DT9 C A :
  C |- c, {A: previous A =>> previous^ A}
| DT10 C Al Ar :
  C |- c, {A: previous^ (Al -> Ar) <=> (previous^ Al -> previous^ Ar)}
| DT11 C Al Ar :
  C |- c, {A: alwaysp (Al -> Ar) =>> (alwaysp Al -> alwaysp Ar)}
| DT12 C A :
  C |- c, {A: always A -> always previous^ A}
| DT13 C A :
  C |- c, {A: (A =>> previous^ A) -> (A =>> alwaysp A)}
| DT14 C Al Ar :
  C |- c, {A: (Al backto Ar) <=> (Ar \/ (Al /\ previous^ (Al backto Ar)))}
| DT15 C :
  C |- c, previous^ AFalse
(* Temporal logic mixed *)
| DT16 C A :
  C |- c, {A: A =>> next previous A}
| DT17 C A :
  C |- c, {A: A =>> previous^ next A}
(* Temporal logic rules *)
| DTGeneralization C A :
  C |- c, A ->
  C |- c, {A: always A}
| DT18 C v A :
  C |- c, {A: (forall: v, next A) <=> (next forall: v, A)}
(* Program logic *)
| DPNode C :
  C |- c, {A: always ("n" \in "Nodes")}
| DPIR C te :
  C |- c, {A:
    when[]-> te =>>
    (("Fs'" $ "Fn", "Fors", "Fois") = request c $ "Fn" $ ("Fs" $ "Fn") $ te)
  }
| DPII C ti te :
  C |- c, {A:
    when[ti]<- te =>>
    (("Fs'" $ "Fn", "Fors", "Fois") =
      indication c $ "Fn" $ ("Fs" $ "Fn") $ (ti, te))
  }
| DPPe C :
  C |- c, {A:
    when[]~> CPer =>>
    (("Fs'" $ "Fn", "Fors", "Fois") =
      periodic c $ "Fn" $ ("Fs" $ "Fn"))
  }
| DPOR C tn ti te :
  C |- c, {A:
    when-on[tn] ((ti, te) \in "Fors" /\ when-self) =>>
    eventually^ when-on[tn] when[ti]-> te
  }
| DPOI C tn te :
  C |- c, {A:
    when-on[tn] (te \in "Fois" /\ when-self) =>>
    eventually^ when-on[tn] when[]<- te
  }
| DPOR' C tn ti te :
  C |- c, {A:
    eventuallyp^ when-on[tn] when[ti]-> te =>>
    when-on[tn] ((ti, te) \in "Fors" /\ when-self)
  }
| DPOI' C tn te :
  C |- c, {A:
    eventuallyp^ when-on[tn] when[]<- te =>>
    when-on[tn] (te \in "Fois" /\ when-self)
  }
| DPInit C :
  C |- c, {A: self ("Fs" = fun: initialize c $ #0)}
| DPPostPre C ts :
  C |- c, {A: self ("Fs'" = ts <=> next ("Fs" = ts))}
| DPSEq C tn :
  C |- c, {A:
    "Fn" <> tn =>>
    "Fs'" $ tn = "Fs" $ tn
  }
| DPASelf C :
  C |- c, {A: self always when-self}
(* TODO: SInv *)
| DPCSet C tn :
  C |- c, {A: correct tn <-> tn \in "Correct"}
| DPAPer C tn :
  C |- c, {A:
    correct tn -> always eventually when-on[tn] when[]~> CPer
  }
| DPFLoss C tn tn' tm ti :
  C |- c, {A:
    correct tn' ->
    always eventually when-on[tn] when[ti]-> CFLSend $ tn' $ tm ->
    always eventually when-on[tn'] when[ti]<- CFLDeliver $ tn $ tm
  }
| DPFDup C tn tn' tm ti :
  C |- c, {A:
    always eventually when-on[tn'] when[ti]<- CFLDeliver $ tn $ tm ->
    always eventually when-on[tn] when[ti]-> CFLSend $ tn' $ tm
  }
| DPNForge C tn tn' tm ti :
  C |- c, {A:
    when-on[tn'] when[ti]<- CFLDeliver $ tn $ tm =>>
    eventuallyp when-on[tn] when[ti]-> CFLSend $ tn' $ tm
  }
(* TODO: UniOR *)
(* TODO: UniOI *)
where "C |- c , A" := (derives c C A).

Hint Constructors derives.

(* Rewriting *)
Fixpoint rewrite_entails C c Ae Ae' (H : C |- c, {A: Ae =>> Ae'}) A :=
  if A == Ae then Ae' else
  match A with
  | AFalse => A
  | APredicate _ => A
  | ANot A => ANot (rewrite_entails H A)
  | AOr Al Ar => AOr (rewrite_entails H Al) (rewrite_entails H Ar)
  | AForAll v A => AForAll v (rewrite_entails H A)
  | AUntil' Al Ar => AUntil' (rewrite_entails H Al) (rewrite_entails H Ar)
  | ASince' Al Ar => ASince' (rewrite_entails H Al) (rewrite_entails H Ar)
  | ASelf A => ASelf (rewrite_entails H A)
  end.

Lemma rewrite_entails_correct C c Ae Ae' (H : C |- c, {A: Ae =>> Ae'}) A :
  C |- c, rewrite_entails H A -> C |- c, A.
Proof.
Admitted. (* TODO *)

Definition congruent_left_right C c Al Ar (H : C |- c, {A: Al <=> Ar}) :
  C |- c, {A: Al =>> Ar}.
Proof.
  apply DSCut with (A1 := {A: Al <=> Ar}); first by [].
  apply DSAndL, DSAxiom.
Defined.

Definition congruent_right_left C c Al Ar (H : C |- c, {A: Al <=> Ar}) :
  C |- c, {A: Ar =>> Al}.
Proof.
  apply DSCut with (A1 := {A: Al <=> Ar}); first by [].
  apply DSAndL, DSExchange, DSAxiom.
Defined.

(* Derived rules and lemmas *)

Lemma Lemma76 C c A1 A2 :
  C |- c, {A: A1 =>> A2} ->
  C |- c, {A: always A1} ->
  C |- c, {A: always A2}.
Proof.
Admitted. (* TODO *)

Lemma Lemma77 C c A1 A2 A3 :
  C |- c, {A: A1 =>> A2} ->
  C |- c, {A: A2 =>> A3} ->
  C |- c, {A: A1 =>> A3}.
Proof.
Admitted. (* TODO *)

Lemma Lemma78_1 C c A1 A2 :
  C |- c, {A: A1 =>> A2} ->
  C |- c, {A: (next A1) =>> next A2}.
Proof.
Admitted. (* TODO *)

Lemma Lemma78_2 C c A1 A2 :
  C |- c, {A: A1 <=> A2} ->
  C |- c, {A: (next A1) <=> (next A2)}.
Proof.
Admitted. (* TODO *)

Lemma Lemma79 C c A :
  C |- c, {A: A =>> next A} ->
  C |- c, {A: A =>> always A}.
Proof.
Admitted. (* TODO *)

Lemma Lemma80 C c A :
  C |- c, {A: always A =>> A}.
Proof.
Admitted. (* TODO *)

Lemma Lemma81 C c A1 A2 :
  C |- c, {A: always (A1 /\ A2) <=> always A1 /\ always A2}.
Proof.
Admitted. (* TODO *)

Lemma Lemma83_1 C c A :
  C |- c, {A: eventuallyp A <=> eventuallyp eventuallyp A}.
Proof.
Admitted. (* TODO *)

Lemma Lemma83_2 C c A :
  C |- c, {A: eventuallyp^ eventuallyp^ A =>> eventuallyp^ A}.
Proof.
Admitted. (* TODO *)

Lemma Lemma83_3 C c A :
  C |- c, {A: eventuallyp eventuallyp^ A =>> eventuallyp^ A}.
Proof.
Admitted. (* TODO *)

Lemma Lemma83_4 C c A :
  C |- c, {A: eventuallyp^ eventuallyp A =>> eventuallyp^ A}.
Proof.
Admitted. (* TODO *)

Lemma Lemma84 C c A :
  C |- c, {A: eventually A <=> eventually eventually A}.
Proof.
Admitted. (* TODO *)

Lemma Lemma85 C c A1 A2 A3 :
  C |- c, {A: A1 =>> eventuallyp A2} ->
  C |- c, {A: A2 =>> eventuallyp A3} ->
  C |- c, {A: A1 =>> eventuallyp A3}.
Proof.
Admitted. (* TODO *)

Lemma Lemma86 C c A1 A2 A3 :
  C |- c, {A: A1 =>> eventually A2} ->
  C |- c, {A: A2 =>> eventually A3} ->
  C |- c, {A: A1 =>> eventually A3}.
Proof.
Admitted. (* TODO *)

Lemma Lemma87 C c A :
  C |- c, {A: A =>> eventuallyp A}.
Proof.
Admitted. (* TODO *)

Lemma Lemma90 C c A :
  C |- c, {A: (self ~A) <=> ~self A}.
Proof.
Admitted. (* TODO *)

Lemma Lemma91 C c A :
  C |- c, {A: A -> previous^ next A}.
Proof.
Admitted. (* TODO *)

Lemma Lemma94 C c A1 A2 :
  C |- c, {A: ((A1 =>> A2) /\ A1) -> A2}.
Proof.
Admitted. (* TODO *)

Lemma Lemma96_1 C c A1 A2 A3 :
  C |- c, {A: (A1 =>> eventually A2) /\ (A2 =>> A3) -> A1 =>> eventually A3}.
Proof.
Admitted. (* TODO *)

Lemma Lemma96_2 C c A1 A2 A3 :
  C |- c, {A: (A1 =>> eventuallyp A2) /\ (A2 =>> A3) -> A1 =>> eventuallyp A3}.
Proof.
Admitted. (* TODO *)

Lemma Lemma96_3 C c A1 A2 A3 :
  C |- c, {A: (A1 =>> eventuallyp^ A2) /\ (A2 =>> A3) -> A1 =>> eventuallyp^ A3}.
Proof.
Admitted. (* TODO *)

Lemma Lemma97 C c A1 A2 A3 :
  C |- c, {A: (A1 =>> always A2) /\ (A2 =>> A3) -> A1 =>> always A3}.
Proof.
Admitted. (* TODO *)

Lemma Lemma98_1 C c A :
  C |- c, {A: eventuallyp always A =>> A}.
Proof.
Admitted. (* TODO *)

Lemma Lemma98_2 C c A :
  C |- c, {A: eventuallyp always^ A =>> A}.
Proof.
Admitted. (* TODO *)

Lemma Lemma98_3 C c A :
  C |- c, {A: eventuallyp^ always A =>> A}.
Proof.
Admitted. (* TODO *)

Lemma Lemma100 C c A :
  C |- c, {A: A -> (alwaysp^ (A =>> self A) =>> A)}.
Proof.
Admitted. (* TODO *)

Lemma Lemma102_1 C c A1 A2 :
  C |- c, {A: (eventually A1 /\ eventually A2) =>>
    ((A1 <-> A2) \/
      eventually (A1 /\ eventually A2) \/
      eventually (A2 /\ eventually A1))}.
Proof.
Admitted. (* TODO *)

Lemma Lemma102_2 C c A1 A2 :
  C |- c, {A: (eventuallyp A1 /\ eventuallyp A2) =>>
    ((A1 <-> A2) \/
      eventuallyp (A1 /\ eventuallyp A2) \/
      eventuallyp (A2 /\ eventuallyp A1))}.
Proof.
Admitted. (* TODO *)

Lemma Lemma102_3 C c A1 A2 :
  C |- c, {A: (eventuallyp A1 /\ eventually A2) =>>
      eventuallyp (A1 /\ eventually A2)}.
Proof.
Admitted. (* TODO *)

Lemma Lemma103_1 C c A :
  C |- c, {A: (eventually A /\ always^ ~A) =>> A}.
Proof.
Admitted. (* TODO *)

Lemma Lemma103_2 C c A :
  C |- c, {A: (eventuallyp A /\ alwaysp^ ~A) =>> A}.
Proof.
Admitted. (* TODO *)

Lemma Lemma104 C c A :
  C |- c, {A: eventuallyp A =>> always eventuallyp A}.
Proof.
Admitted. (* TODO *)

Lemma Lemma105_1 C c A :
  C |- c, {A: (A =>> always^ ~A) -> (A =>> alwaysp^ ~A)}.
Proof.
Admitted. (* TODO *)

Lemma Lemma105_2 C c A :
  C |- c, {A: (A =>> alwaysp^ ~A) -> (A =>> always^ ~A)}.
Proof.
Admitted. (* TODO *)

Lemma Lemma106 C c A1 A2 :
  C |- c, {A: (A1 =>> eventuallyp (A1 =>> A2)) -> (A1 =>> A2)}.
Proof.
Admitted. (* TODO *)

Lemma Lemma107 C c A :
  C |- c, {A: (alwaysp^ A =>> A) -> always A}.
Proof.
Admitted. (* TODO *)

Lemma Lemma108 C c A1 A2 :
  C |- c, {A: ((alwaysp^ A1 /\ alwaysp^ A2) =>>
    (A1 /\ A2)) -> always (A1 /\ A2)}.
Proof.
Admitted. (* TODO *)

Lemma Lemma109_1 C c A :
  C |- c, {A: eventuallyp eventually A <=> eventually A \/ eventuallyp A}.
Proof.
Admitted. (* TODO *)

Lemma Lemma109_2 C c A :
  C |- c, {A: eventuallyp^ eventually A =>> eventually A \/ eventuallyp A}.
Proof.
Admitted. (* TODO *)

Lemma Lemma109_3 C c A :
  C |- c, {A: eventually eventuallyp A =>> eventually A \/ eventuallyp A}.
Proof.
Admitted. (* TODO *)

Lemma Lemma109_4 C c A :
  C |- c, {A: eventually eventuallyp^ A =>> eventually A \/ eventuallyp A}.
Proof.
Admitted. (* TODO *)

Lemma Lemma109_5 C c A :
  C |- c, {A: eventuallyp^ eventually^ A =>> eventually A \/ eventuallyp A}.
Proof.
Admitted. (* TODO *)

Lemma Lemma111 C c A :
  C |- c, {A: (eventuallyp A) <=> self eventuallyp^ A}.
Proof.
Admitted. (* TODO *)

Lemma Lemma112 C c A1 A2 :
  C |- c, {A: (eventually A1 /\ always A2) =>> eventually (A1 /\ always A2)}.
Proof.
Admitted. (* TODO *)

Lemma Lemma114 C c A :
  C |- c, {A: (~eventuallyp^ A) =>> alwaysp^ ~A}.
Proof.
Admitted. (* TODO *)

Lemma Lemma115 C c A :
  C |- c, {A: (alwaysp^ A) <=> alwaysp previous^ A}.
Proof.
Admitted. (* TODO *)

Lemma Lemma116 C c A1 A2 :
  C |- c, {A: (A1 /\ eventuallyp^ A2) =>> eventuallyp^ (A2 /\ eventually A1)}.
Proof.
Admitted. (* TODO *)

Lemma Lemma117 C c A :
  C |- c, {A: (alwaysp A /\ always A) =>>
    alwaysp alwaysp^ A /\ always alwaysp^ A}.
Proof.
Admitted. (* TODO *)

Lemma Lemma118 C c A :
  C |- c, {A: (eventuallyp^ self A) <=> eventuallyp A}.
Proof.
Admitted. (* TODO *)

(*
InvS''
APerSA
*)

Lemma IROI C c (S : term -> predicate) tn te te' :
  C |- c, {A:
    # (S "s") /\
      te' = {t: let: (%, #, %) := request c $ tn $ "s" $ te in: #0} ->
    te' \in "Fois"} ->
  C |- c, {A:
    when-on[tn] when[]-> te /\ # (S {t: "Fs" $ tn}) =>>
    eventually when-on[tn] when[]<- te'
  }.
Proof.
Admitted. (* TODO *)

Lemma IIOI C c (S : term -> predicate) tn ti te te' :
  C |- c, {A:
    # (S "s") /\
      te' = {t: let: (%, #, %) := indication c $ tn $ "s" $ (ti, te) in: #0} ->
    te' \in "Fois"} ->
  C |- c, {A:
    when-on[tn] when[ti]<- te /\ # (S {t: "Fs" $ tn}) =>>
    eventually when-on[tn] when[]<- te'
  }.
Proof.
Admitted. (* TODO *)
