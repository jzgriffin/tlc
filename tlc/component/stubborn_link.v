Require Import mathcomp.ssreflect.seq.
Require Import mathcomp.ssreflect.ssreflect.
Require Import tlc.component.component.
Require Import tlc.logic.all_logic.
Require Import tlc.semantics.all_semantics.
Require Import tlc.syntax.all_syntax.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Stubborn link component *)
Definition stubborn_link :=
  let flc := 0 in
  Component
  (* initialize *)
  {t: fun:
    (* #0 = n *)
    []
  }
  (* request *)
  {t: fun: fun: fun:
    (* #(0, 0) = ir *)
    (* #(1, 0) = s *)
    (* #(2, 0) = n *)
    match: #0 with: CSLSend $ # $ #
    then:
      (* #(0, 0) = n' *)
      (* #(0, 1) = m *)
      (#(2, 0) \union [(#0, #1)],
        [(flc, CFLSend $ #0 $ #1)],
        [])
    else: TFailure
  }
  (* indication *)
  {t: fun: fun: fun:
    (* #(0, 0) = ii *)
    (* #(1, 0) = s *)
    (* #(2, 0) = n' *)
    match: #0 with: (flc, CFLDeliver $ # $ #)
    then:
      (* #(0, 0) = n *)
      (* #(0, 1) = m *)
      (#(2, 0), [], [CSLDeliver $ #0 $ #1])
    else: TFailure
  }
  (* periodic *)
  {t: fun: fun:
    (* #(0, 0) = s *)
    (* #(1, 0) = n *)
    let: # := (fun: let: (#, #) := #0 in:
      (flc, CFLSend $ #0 $ #1)) <$> #(0, 0) in:
    (#(1, 0), #0, [])
  }.

(* Specification *)

(* Stubborn delivery
 * If a correct node n sends a message m to a correct node n',
 * then n' deliver m infinitely often *)
Theorem SL_1 tn tn' tm : [::] |- stubborn_link, {A:
  correct tn /\ correct tn' ->
  when-on[tn] when[]-> CSLSend $ tn' $ tm =>>
  always eventually when-on[tn'] when[]<- CSLDeliver $ tn $ tm
}.
Proof.
  apply DSIfR, DSAndL.
  (*apply rewrite_entails_correct with
    (H := congruent_left_right (Lemma84 _ _
      {A: when-on["n'"] when[]<- CSLDeliver $ "n" $ "m"})).
  rewrite /=.*)
Admitted. (* TODO *)

(* No-forge
 * If a node n delivers a emssage m with sender n', then m was
 * previously sent to n by n' *)
Theorem SL_2 : [::] |- stubborn_link, {A:
  forall: "n", forall: "n'", forall: "m",
  (when-on["n"] when[]<- {t: CSLDeliver $ "n'" $ "m"}) <~
  (when-on["n'"] when[]-> {t: CSLSend $ "n" $ "m"})
}.
Proof.
Admitted. (* TODO *)
