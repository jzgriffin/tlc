Require Import Coq.Lists.List.
Require Import TLC.Component.
Require Import TLC.FairLossLink.
Require Import TLC.ProgramLogic.
Require Import TLC.SequentLogic.
Require Import TLC.TemporalLogic.
Require Import TLC.Term.
Require Coq.Vectors.Vector.

Import ListNotations.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section stubborn_link.

  Variable node : Type.
  Variable message : Type.

  Inductive request_sl : Type :=
  | Send_sl : node -> message -> request_sl.

  Inductive indication_sl : Type :=
  | Deliver_sl : node -> message -> indication_sl.

  Section sub_interfaces.

    Import Vector.VectorNotations.

    Definition sub_interfaces_sl : interfaces :=
      existT _ _ [(request_fl node message, indication_fl node message)].

  End sub_interfaces.

  Definition state_sl := list (node * message).

  Definition slc :=
    let initialize n := [] in
    let request n s ir :=
      match ir with
      | Send_sl n' m =>
        let s' := (n', m) :: s in
        let ors := [Send_fl n' m] in
        let ois := [] in
        (s', ors, ois)
      end in
    let indication n' s ii :=
      match ii with
      | Deliver_fl n m =>
        let s' := s in
        let ors := [] in
        let ois := [Deliver_sl n m] in
        (s', ors, ois)
      end in
    let periodic n s :=
      let s' := s in
      let ors := map (fun p => Send_fl (fst p) (snd p)) s in
      let ois := [] in
      (s', ors, ois) in
    @Component node message request_sl indication_sl sub_interfaces_sl state_sl
      initialize request indication periodic.

  Lemma slc_ir_term (x : term slc request_sl) : term slc (ir_event slc).
  Proof. assumption. Qed.
  Lemma slc_oi_term (x : term slc indication_sl) : term slc (oi_event slc).
  Proof. assumption. Qed.

  Theorem SL_1 (n n' : term slc node) (m : term slc message) : [] |- slc, (
    Correct <- n /\ Correct <- n' ->
    (on: n, when[]->: slc_ir_term (^Send_sl <- n' <- m)) =>>
    always: eventually:
      on: n', when[]<-: slc_oi_term (^Deliver_sl <- n <- m)
  ).
  Proof.
  Admitted. (* TODO *)

  Theorem SL_2 (n n' : term slc node) (m : term slc message) : [] |- slc, (
    (on: n, when[]<-: slc_oi_term (^Deliver_sl <- n' <- m)) <~
    (on: n', when[]->: slc_ir_term (^Send_sl <- n <- m))
  ).
  Proof.
  Admitted. (* TODO *)

End stubborn_link.
