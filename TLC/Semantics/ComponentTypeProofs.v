Require Import TLC.Semantics.Type.
Require Import Coq.Lists.List.
Require TLC.Concrete.Component.
Require TLC.Syntax.Component.
Require TLC.Typing.Component.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Record component_type_proofs P : Type :=
  ComponentTypeProofs {
    ctp_component : TLC.Typing.Component.component P;
    (* Basic types *)
    denote_ir_event : [t:TLC.Typing.Component.ir_event ctp_component | P] =
      TLC.Concrete.Component.ir_event
        (TLC.Syntax.Component.concrete_component
          (TLC.Typing.Component.syntactic_component ctp_component));
    denote_oi_event : [t:TLC.Typing.Component.oi_event ctp_component | P] =
      TLC.Concrete.Component.oi_event
        (TLC.Syntax.Component.concrete_component
          (TLC.Typing.Component.syntactic_component ctp_component));
    denote_state : [t:TLC.Typing.Component.state ctp_component | P] =
      TLC.Concrete.Component.state
        (TLC.Syntax.Component.concrete_component
          (TLC.Typing.Component.syntactic_component ctp_component));
    denote_or_event : [t:TLC.Typing.Component.or_event ctp_component | P] =
      TLC.Concrete.Component.or_event
        (TLC.Syntax.Component.concrete_component
          (TLC.Typing.Component.syntactic_component ctp_component));
    denote_ii_event : [t:TLC.Typing.Component.ii_event ctp_component | P] =
      TLC.Concrete.Component.ii_event
        (TLC.Syntax.Component.concrete_component
          (TLC.Typing.Component.syntactic_component ctp_component));
  }.

(* Derived types *)

Lemma denote_event {P} (CTP : component_type_proofs P) :
  [t:TLC.Typing.Component.event (ctp_component CTP) | P] =
    TLC.Concrete.Component.event
      (TLC.Syntax.Component.concrete_component
        (TLC.Typing.Component.syntactic_component (ctp_component CTP))).
Proof.
  simpl; now rewrite
    (denote_ir_event CTP), (denote_oi_event CTP),
    (denote_or_event CTP), (denote_ii_event CTP).
Qed.

Lemma denote_states {P} (CTP : component_type_proofs P) :
  [t:TLC.Typing.Component.states (ctp_component CTP) | P] =
    TLC.Concrete.Component.states
      (TLC.Syntax.Component.concrete_component
        (TLC.Typing.Component.syntactic_component (ctp_component CTP))).
Proof.
  simpl; now rewrite (denote_state CTP).
Qed.

Lemma denote_output {P} (CTP : component_type_proofs P) :
  [t:TLC.Typing.Component.output (ctp_component CTP) | P] =
    TLC.Concrete.Component.output
      (TLC.Syntax.Component.concrete_component
        (TLC.Typing.Component.syntactic_component (ctp_component CTP))).
Proof.
  simpl; now rewrite
    (denote_state CTP), (denote_or_event CTP), (denote_oi_event CTP).
Qed.
