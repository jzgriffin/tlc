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

  (* Meaning: Within context Z for component C, A is true *)
  Reserved Notation "Z ||- A" (at level 70, no associativity).

  (* These rules and axioms use the following naming convention:
   * - Every constructor begins with D, followed by one of:
   *    - A for rules/axioms specific to this implementation
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
  (* Variable context *)
  | DVThin Delta Gamma x A :
    (* Introduce a fresh rigid variable to the context *)
    x \notin ((context_rigids (Context Delta Gamma)) ++
      (assertion_rigids A)) ->
    Context Delta Gamma ||- A ->
    Context (x :: Delta) Gamma ||- A
  | DVContraction Delta Gamma x A :
    Context (x :: x :: Delta) Gamma ||- A ->
    Context (x :: Delta) Gamma ||- A
  | DVExchange Delta1 Delta2 Gamma x1 x2 A :
    Context (x1 :: Delta1 ++ x2 :: Delta2) Gamma ||- A ->
    Context (x2 :: Delta1 ++ x1 :: Delta2) Gamma ||- A

  (* Reduction *)
  | DReduceEq Z t t' :
    (* Every term is equal to its reduction *)
    [[t t]] = Success t' ->
    Z ||- {-A always (t = t') -}
  | DReduceCong Z A A' :
    (* Every assertion is congruent to its reduction *)
    [[A A]] = Success A' ->
    Z ||- {-A A <=> A' -}

  (* Injection *)
  | DInjection Delta Gamma t1 t2 c xh1 xh2 xt1 xt2 :
    term_construction t1 = Some (c, rcons xh1 xt1) ->
    term_construction t2 = Some (c, rcons xh2 xt2) ->
    size xh1 = size xh2 ->
    Context Delta Gamma ||- {-A
      t1 = t2 ->
      foldr (fun '(x1, x2) A => {-A x1 = x2 /\ A -})
        {-A xt1 = xt2 -} (zip xh1 xh2)
    -}

  (* Case analysis *)
  | DCaseAnalysis Z a cs A :
    (* Assumes that cs type-checks with a and is exhaustive *)
    destruct_cases a cs = Some A ->
    Z ||- A

  (* Sequent logic *)
  | DSFalse Delta Gamma A :
    Context Delta (AFalse :: Gamma) ||- A
  | DSAxiom Delta Gamma A :
    Context Delta (A :: Gamma) ||- A
  | DSThin Delta Gamma H A :
    Context Delta Gamma ||- A ->
    Context Delta (H :: Gamma) ||- A
  | DSContraction Delta Gamma H A :
    Context Delta (H :: H :: Gamma) ||- A ->
    Context Delta (H :: Gamma) ||- A
  | DSExchange Delta Gamma1 Gamma2 H1 H2 A :
    Context Delta (H1 :: Gamma1 ++ H2 :: Gamma2) ||- A ->
    Context Delta (H2 :: Gamma1 ++ H1 :: Gamma2) ||- A
  | DSCut Delta Gamma H A :
    Context Delta Gamma ||- H ->
    Context Delta (H :: Gamma) ||- A ->
    Context Delta Gamma ||- A
  | DSNotP Delta Gamma H A :
    Context Delta Gamma ||- H ->
    Context Delta ({-A ~H -} :: Gamma) ||- A
  | DSNotC Delta Gamma A :
    Context Delta (A :: Gamma) ||- AFalse ->
    Context Delta Gamma ||- {-A ~A -}
  | DSOrP Delta Gamma H1 H2 A :
    Context Delta (H1 :: Gamma) ||- A ->
    Context Delta (H2 :: Gamma) ||- A ->
    Context Delta ({-A H1 \/ H2 -} :: Gamma) ||- A
  | DSOrCL Delta Gamma A1 A2 :
    Context Delta Gamma ||- A1 ->
    Context Delta Gamma ||- {-A A1 \/ A2 -}
  | DSOrCR Delta Gamma A1 A2 :
    Context Delta Gamma ||- A2 ->
    Context Delta Gamma ||- {-A A1 \/ A2 -}
  | DSAndP Delta Gamma H1 H2 A :
    Context Delta (H1 :: H2 :: Gamma) ||- A ->
    Context Delta ({-A H1 /\ H2 -} :: Gamma) ||- A
  | DSAndC Delta Gamma A1 A2 :
    Context Delta Gamma ||- A1 ->
    Context Delta Gamma ||- A2 ->
    Context Delta Gamma ||- {-A A1 /\ A2 -}
  | DSIfP Delta Gamma Hp Hc A :
    Context Delta Gamma ||- Hp ->
    Context Delta (Hc :: Gamma) ||- A ->
    Context Delta ({-A Hp -> Hc -} :: Gamma) ||- A
  | DSIfC Delta Gamma Ap Ac :
    Context Delta (Ap :: Gamma) ||- Ac ->
    Context Delta Gamma ||- {-A Ap -> Ac -}
  | DSForAllP Delta Gamma t H H' A :
    term_closed_in [::] Delta t ->
    open_assertion [:: t] H = Success H' ->
    Context Delta (H' :: Gamma) ||- A ->
    Context Delta ({-A forall: H -} :: Gamma) ||- A
  | DSForAllC Delta Gamma x A A' :
    x \notin ((context_rigids (Context Delta Gamma)) ++
      (assertion_rigids {-A forall: A -})) ->
    open_assertion [:: TVariable x] A = Success A' ->
    Context (x :: Delta) Gamma ||- A' ->
    Context Delta Gamma ||- {-A forall: A -}
  | DSExistsP Delta Gamma x H H' A :
    x \notin ((context_rigids (Context Delta Gamma)) ++
      (assertion_rigids {-A exists: A -})) ->
    open_assertion [:: TVariable x] H = Success H' ->
    Context (x :: Delta) (H' :: Gamma) ||- A ->
    Context Delta ({-A exists: H -} :: Gamma) ||- A
  | DSExistsC Delta Gamma t A A' :
    term_closed_in [::] Delta t ->
    open_assertion [:: t] A = Success A' ->
    Context Delta Gamma ||- A' ->
    Context Delta Gamma ||- {-A exists: A -}

  (* Temporal logic future *)
  | DT1 Delta Gamma A :
    Context Delta Gamma ||- {-A always A -> A -}
  | DT2 Delta Gamma A :
    Context Delta Gamma ||- {-A (next ~A) <=> ~next A -}
  | DT3 Delta Gamma A1 A2 :
    Context Delta Gamma ||- {-A (next (A1 -> A2)) <=> (next A1 -> next A2) -}
  | DT4 Delta Gamma A1 A2 :
    Context Delta Gamma ||- {-A (always (A1 -> A2)) =>> (always A1 -> always A2) -}
  | DT5 Delta Gamma A :
    Context Delta Gamma ||- {-A (always A) -> always next A -}
  | DT6 Delta Gamma A :
    Context Delta Gamma ||- {-A (A =>> next A) -> (A =>> always A) -}

  (* Temporal logic past *)
  | DT9 Delta Gamma A :
    Context Delta Gamma ||- {-A previous A =>> previous^ A -}
  | DT10 Delta Gamma A1 A2 :
    Context Delta Gamma ||- {-A previous^ (A1 -> A2) <=> (previous^ A1 -> previous^ A2) -}
  | DT11 Delta Gamma A1 A2 :
    Context Delta Gamma ||- {-A alwaysp (A1 -> A2) =>> (alwaysp A1 -> alwaysp A2) -}
  | DT12 Delta Gamma A :
    Context Delta Gamma ||- {-A always A -> always previous^ A -}
  | DT13 Delta Gamma A :
    Context Delta Gamma ||- {-A (A =>> previous^ A) -> (A =>> alwaysp A) -}
  | DT15 Delta Gamma :
    Context Delta Gamma ||- previous^ AFalse

  (* Temporal logic mixed *)
  | DT16 Delta Gamma A :
    Context Delta Gamma ||- {-A A =>> next previous A -}
  | DT17 Delta Gamma A :
    Context Delta Gamma ||- {-A A =>> previous^ next A -}

  (* Temporal logic rules *)
  | DTGeneralization Delta Gamma A :
    non_temporal_assertion A ->
    Context Delta Gamma ||- A ->
    Context Delta Gamma ||- {-A always A -}
  | DT18 Delta Gamma A :
    Context Delta Gamma ||- {-A (forall: next A) <=> (next forall: A) -}

  (* Program logic *)
  | DPNode Delta Gamma :
    Context Delta Gamma ||- {-A
      forall: (* n *)
      always ($$0 \in UNodes)
    -}
  | DPIR Delta Gamma :
    Context Delta Gamma ||- {-A
      forall: (* e *)
      event []-> $$0 =>>
      (Fs' ' Fn, Fors, Fois) =
        request C ' Fn ' (Fs ' Fn) ' $$0
    -}
  | DPII Delta Gamma :
    Context Delta Gamma ||- {-A
      forall: forall: (* i, e *)
      event [$$1]<- $$0 =>>
      (Fs' ' Fn, Fors, Fois) =
        indication C ' Fn ' (Fs ' Fn) ' ($$1, $$0)
    -}
  | DPPe Delta Gamma :
    Context Delta Gamma ||- {-A
      event []~> CPE =>>
      (Fs' ' Fn, Fors, Fois) =
        periodic C ' Fn ' (Fs ' Fn)
    -}
  | DPOR Delta Gamma :
    Context Delta Gamma ||- {-A
      forall: forall: forall: (* n, i, e *)
      on $$2, (self-event /\ ($$1, $$0) \in Fors) =>>
      eventually^ on $$2, event [$$1]-> $$0
    -}
  | DPOI Delta Gamma :
    Context Delta Gamma ||- {-A
      forall: forall: (* n, e *)
      on $$1, (self-event /\ $$0 \in Fois) =>>
      eventually^ on $$1, event []<- $$0
    -}
  | DPOR' Delta Gamma :
    Context Delta Gamma ||- {-A
      forall: forall: forall: (* n, i, e *)
      on $$2, event [$$1]-> $$0 =>>
      eventuallyp^ (self-event /\ on $$2, (($$1, $$0) \in Fors))
    -}
  | DPOI' Delta Gamma :
    Context Delta Gamma ||- {-A
      forall: forall: (* n, e *)
      on $$1, event []<- $$0 =>>
      eventuallyp^ (self-event /\ on $$1, ($$0 \in Fois))
    -}
  | DPInit Delta Gamma :
    Context Delta Gamma ||- {-A self (Fs = fun: initialize C ' $$0) -}
  | DPPostPre Delta Gamma :
    Context Delta Gamma ||- {-A
      forall: (* s *)
      self (Fs' = $$0 <=> next (Fs = $$0))
    -}
  | DPSEq Delta Gamma :
    Context Delta Gamma ||- {-A
      forall: (* n *)
      Fn <> $$0 =>> Fs' ' $$0 = Fs ' $$0
    -}
  | DPASelf Delta Gamma :
    Context Delta Gamma ||- {-A self always self-event -}
  | DPSInv_1 Delta Gamma A :
    Context Delta Gamma ||- {-A self A -> restrict_assertion {-A self-event -} A -}
  | DPSInv_2 Delta Gamma A :
    Context Delta Gamma ||- {-A restrict_assertion {-A self-event -} A -> self A -}
  | DPAPer Delta Gamma :
    Context Delta Gamma ||- {-A
      forall: (* n *)
      $$0 \in UCorrect -> always eventually on $$0, event []~> CPE
    -}
  | DPFLoss Delta Gamma :
    Context Delta Gamma ||- {-A
      forall: forall: forall: forall: (* n, n', m, i *)
      $$2 \in UCorrect ->
      always^ eventually^ on $$3, event [$$0]-> CFLSend ' $$2 ' $$1 ->
      always^ eventually^ on $$2, event [$$0]<- CFLDeliver ' $$3 ' $$1
    -}
  | DPFDup Delta Gamma :
    Context Delta Gamma ||- {-A
      forall: forall: forall: forall: (* n, n', m, i *)
      always eventually on $$2, event [$$0]<- CFLDeliver ' $$3 ' $$1 ->
      always eventually on $$3, event [$$0]-> CFLSend ' $$2 ' $$1
    -}
  | DPNForge Delta Gamma :
    Context Delta Gamma ||- {-A
      forall: forall: forall: forall: (* n, n', m, i *)
      on $$2, event [$$0]<- CFLDeliver ' $$3 ' $$1 =>>
      eventuallyp on $$3, event [$$0]-> CFLSend ' $$2 ' $$1
    -}
  (* TODO: UniOR *)
  | DPUniOI Delta Gamma :
    Context Delta Gamma ||- {-A
      forall: forall: forall: (* n, ois, e *)
      (((FCount ' $$0 ' $$1) <= 1) /\
       always^ (self-event /\ Fn = $$2 -> $$0 \notin $$1) /\
       alwaysp^ (self-event /\ Fn = $$2 -> $$0 \notin $$1)) =>>
      (on $$2, event[]<- $$0) =>>
      alwaysp^ (~ on $$2, event[]<- $$0) /\ always^ ~ on $$2, event[]<- $$0
    -}
  where "Z ||- A" := (derives Z A).

End derives.

Notation "Z ||- C , A" := (derives C Z A)
  (at level 70, no associativity).

Hint Constructors derives : core.

(* Extract the context from a syntactic proof *)
Definition derives_context C Z A (H : Z ||- C, A) := Z.

(* Extract the assertion from a syntactic proof *)
Definition derives_assertion C Z A (H : Z ||- C, A) := A.

(* Extract the variables from a syntactic proof *)
Definition derives_rigids Z A :=
  (context_rigids Z) ++ (assertion_rigids A).

(* Determine whether a proof is closed under its bindings *)
Definition derives_closed
  (Delta : context_bindings) (Gamma : context_assumptions) A :=
  all (assertion_closed_in [::] Delta) (A :: Gamma).

(* Every variable within a proof is bound *)
Lemma DClosed (Delta : context_bindings) (Gamma : context_assumptions) A :
  derives_closed Delta Gamma A.
Proof.
Admitted.

(* There is always a fresh variable that does not appear in a syntactic proof *)
Lemma DFresh Z A :
  exists x, x \notin derives_rigids Z A.
Proof.
Admitted.

(* Tactics
 * Some of these tactics are named for their Coq equivalents.  For example,
 * dclear uses the DSThin axiom but operates similarly to clear.
 *)

(* Tactics relating to fresh variables *)
Ltac dclearv := apply DVThin.
Ltac dsimplfresh :=
  repeat match goal with
  | Hf : is_true (_ \notin (derives_rigids _ _)) |- _ =>
    rewrite /derives_rigids /context_rigids /= ?cats0 ?cat0s in Hf
  | Hf : is_true (_ \notin _) |- _ =>
    try rewrite computable_term_rigids ?cats0 ?cat0s in Hf; last by []
  end;
  repeat match goal with
  (* Break down compounds *)
  | Hf : is_true (_ \notin (_ :: _)) |- _ =>
    let Hf' := fresh Hf in
    rewrite in_cons in Hf; move/norP: Hf => [/eqP Hf' Hf]
  | Hf : is_true (_ \notin (_ ++ _)) |- _ =>
    rewrite mem_cat in Hf; move/norP: Hf => Hf
  | Hf : is_true (?x \notin ?ys) /\ is_true (?x \notin _) |- _ =>
    let Hf' := fresh Hf in
    move: Hf => [Hf' Hf]
  (* Remove duplicates and tautologies *)
  | Hf : is_true (_ \notin [::]) |- _ =>
    clear Hf
  | Hf : is_true (?x \notin ?ys), Hf' : is_true (?x \notin ?ys) |- _ =>
    clear Hf'
  | Hf : ?x <> ?y, Hf' : ?x <> ?y |- _ =>
    clear Hf'
  end.
Tactic Notation "dfresh" ident(x) :=
  match goal with
  | |- context[ ?Z ||- _, ?A ] =>
    let Hxf := fresh "Hf_" x in
    case: (DFresh Z A) => x Hxf; dsimplfresh
  end.
Ltac dautofresh :=
  repeat match goal with
  | |- context[ context_rigids _ ] =>
    rewrite /context_rigids /= ?cats0 ?cat0s
  | |- is_true (_ \notin (term_rigids _)) =>
    rewrite computable_term_rigids; last by []
  | |- is_true (_ \notin (_ :: _)) =>
    rewrite in_cons; apply/norP; split; [try by apply/eqP | try by [] ]
  | |- is_true (_ \notin (_ ++ _)) =>
    rewrite mem_cat; apply/norP; split; try by []
  end.

(* Injection tactics *)
Ltac dinject t1_ t2_ :=
  eapply DSCut;
    first (by eapply DInjection with (t1 := t1_) (t2 := t2_));
    simpl.
Ltac dinjection :=
  match goal with
  | |- context[ {-A ?t1_ = ?t2_ -} ] => dinject t1_ t2_
  end.

(* Sequent logic tactics *)
Ltac dexfalso := apply DSFalse.
Ltac dhead := apply DSAxiom.
Ltac dclear := apply DSThin.
Ltac dhave H :=
  match goal with
  | |- derives ?C (Context ?Delta ?Gamma) ?A =>
    apply (@DSCut C Delta Gamma H A)
  end.
Ltac duse L :=
  eapply DSCut; first by repeat dclear; eapply L.
Ltac dnotp := apply DSNotP.
Ltac dnot := apply DSNotC.
Ltac dorp := apply DSOrP.
Ltac dleft := apply DSOrCL.
Ltac dright := apply DSOrCR.
Ltac dsplitp := apply DSAndP.
Ltac dsplit := apply DSAndC.
Ltac difp := apply DSIfP.
Ltac dif := apply DSIfC.
Tactic Notation "dforallp" constr(x) :=
  eapply DSForAllP with (t := x);
  [try by dautoclosed | try by dautoopen | dclean].
Tactic Notation "dforall" ident(y) :=
  dfresh y; eapply DSForAllC with (x := y);
  [dautofresh; try by [] | try by dautoopen | dclean].
Tactic Notation "dexistsp" ident(y) :=
  dfresh y; eapply DSExistsP with (x := y);
  [dautofresh; try by [] | try by dautoopen | dclean].
Tactic Notation "dexists" constr(x) :=
  eapply DSExistsC with (t := x);
  [try by dautoclosed | try by dautoopen | dclean].
