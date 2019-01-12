Require Import TLC.Concrete.Component.
Require Import TLC.Concrete.FairLossLink.
Require Import TLC.Concrete.Orientation.
Require Import TLC.Concrete.PEvent.
Require Import TLC.Concrete.StubbornLink.
Require Import TLC.Parameters.
Require Import TLC.Typing.Component.
Require Import TLC.Typing.Expression.
Require Import TLC.Semantics.ComponentTypeProofs.
Require Import TLC.Semantics.Context.
Require Import TLC.Semantics.Interpretation.
Require Import TLC.Semantics.Type.
Require Import TLC.Utility.HList.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Maps abstract expressions to concrete *)
Fixpoint denote_expression {P} (CTP : component_type_proofs P) {G e t}
  (te : G |-e e : t | (ctp_component CTP)) :
  [I: ctp_component CTP] -> [G: G | P] -> [t: t | P].
Proof.
  refine (match te with
  (* Variables *)
  | TEVariable m _ _ => fun _ GD => hget GD m
  (* Constants *)
  | TECUnit => fun _ _ => tt
  (* Products *)
  | TECPair => fun _ _ => pair
  (* Sums *)
  | TECLeft => fun _ _ => inl
  | TECRight => fun _ _ => inr
  (* Lists *)
  | TECNil => fun _ _ => nil
  | TECCons => fun _ _ => cons
  (* Naturals *)
  | TECZero => fun _ _ => O
  | TECSucc => fun _ _ => S
  (* Orientations *)
  | TECORequest => fun _ _ => ORequest
  | TECOIndication => fun _ _ => OIndication
  | TECOPeriodic => fun _ _ => OPeriodic
  (* Model *)
  | TECNodes => fun I _ => INodes I
  | TECCorrectNodes => fun I _ => ICorrectNodes I
  (* Periodic events *)
  | TECPE => fun _ _ => PE
  (* Fair-loss link request *)
  | TECFLLSend => fun _ _ => @FLLSend P
  (* Fair-loss link indication *)
  | TECFLLDeliver => fun _ _ => @FLLDeliver P
  (* Stubborn link request *)
  | TECSLSend => fun _ _ => @SLSend P
  (* Stubborn link indication *)
  | TECSLDeliver => fun _ _ => @SLDeliver P
  (* Stubborn link functions *)
  | TECSLInitialize => fun _ _ => @initialize _ (sl_component P)
  | TECSLRequest => fun _ _ => @request _ (sl_component P)
  | TECSLIndication => fun _ _ => @indication _ (sl_component P)
  | TECSLPeriodic => fun _ _ => @periodic _ (sl_component P)
  (* Flexible variables *)
  | TEFn => fun I _ => IFn I
  | TEFd => fun I _ => IFd I
  | TEFo => fun I _ => IFo I
  | TEFe => fun I _ => _
  | TEFors => fun I _ => _
  | TEFois => fun I _ => _
  | TEFs => fun I _ => _
  | TEFs' => fun I _ => _
  (* Application *)
  | TEApplication _ _ te1 te2 => fun I GD =>
    let x1 := denote_expression _ _ _ _ _ te1 I GD in
    let x2 := denote_expression _ _ _ _ _ te2 I GD in
    x1 x2
  end).
  - rewrite (denote_event CTP); exact (IFe I).
  - simpl; rewrite (denote_or_event CTP); exact (IFors I).
  - simpl; rewrite (denote_oi_event CTP); exact (IFois I).
  - rewrite (denote_states CTP); exact (IFs I).
  - rewrite (denote_states CTP); exact (IFs' I).
Defined.

Notation "[e: x \ y \ z | w ]" := (denote_expression w x y z)
  (at level 0) : core_scope.
