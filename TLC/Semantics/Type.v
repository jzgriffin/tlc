Require Import TLC.Concrete.FairLossLink.
Require Import TLC.Concrete.Orientation.
Require Import TLC.Concrete.PEvent.
Require Import TLC.Concrete.StubbornLink.
Require Import TLC.Parameters.
Require Import TLC.Typing.Type.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section denote_type.

  Variable P : parameters.

  Reserved Notation "[ x ]" (at level 0).

  (* Maps abstract types to concrete *)
  Fixpoint denote_type t : Type :=
    match t with
    | TUnit => unit
    | TFunction t1 t2 => [t1] -> [t2]
    | TProduct t1 t2 => [t1] * [t2]
    | TSum t1 t2 => [t1] + [t2]
    | TList t1 => list [t1]
    | TNatural => nat
    | TOrientation => orientation
    (* Parameters *)
    | TNode => node P
    | TMessage => message P
    (* Periodic events *)
    | TPEvent => p_event
    (* Fair-loss link *)
    | TFLLRequest => fll_request P
    | TFLLIndication => fll_indication P
    (* Stubborn link *)
    | TSLState => sl_state P
    | TSLRequest => sl_request P
    | TSLIndication => sl_indication P
    end
    where "[ x ]" := (denote_type x) : type_scope.

End denote_type.

(* Notations for denoting types *)
Notation "[t: x | y ]" := (denote_type y x) (at level 0) : type_scope.
