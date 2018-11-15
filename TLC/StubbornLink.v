Require Import Coq.Lists.List.
Require Import TLC.Component.
Require Import TLC.FairLossLink.
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

End stubborn_link.
