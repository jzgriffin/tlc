Require Import TLC.Concrete.Component.
Require Import TLC.Concrete.FairLossLink.
Require Import TLC.Concrete.Interface.
Require Import TLC.Concrete.Stack.
Require Import TLC.Parameters.
Require Import TLC.Utility.HList.
Require Import Coq.Lists.List.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section stubborn_link.

  Import ListNotations.

  Variable P : parameters.

  (* Input request type for the stubborn link *)
  Inductive sl_request : Type :=
  | SLSend (n : node P) (m : message P).

  (* Output indication type for the stubborn link *)
  Inductive sl_indication : Type :=
  | SLDeliver (n : node P) (m : message P).

  (* Interface for the stubborn link *)
  Definition sl_interface : interface := (sl_request, sl_indication).

  (* Interfaces for the sub-components of the stubborn link *)
  Definition sl_sub_interfaces : interfaces := [fll_interface P].

  (* State type for the stubborn link *)
  Definition sl_state := list (node P * message P).

  (* Stubborn link component *)
  Definition sl_component :=
    let initialize n := [] in
    let request n s ir :=
      match ir with
      | SLSend n' m =>
        let s' := (n', m) :: s in
        let ors := [FLLSend n' m] in
        let ois := [] in
        (s', ors, ois)
      end in
    let indication n' s ii :=
      match ii with
      | FLLDeliver n m =>
        let s' := s in
        let ors := [] in
        let ois := [SLDeliver n m] in
        (s', ors, ois)
      end in
    let periodic n s :=
      let s' := s in
      let ors := map (fun p => FLLSend (fst p) (snd p)) s in
      let ois := [] in
      (s', ors, ois)
      in
    @Component P sl_request sl_indication sl_sub_interfaces
      sl_state initialize request indication periodic.

  (* Stubborn link stack *)
  Definition sl_stack : stack P sl_interface :=
    @Stack _ sl_component [FairLossLink P].

End stubborn_link.
