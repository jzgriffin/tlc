From mathcomp.ssreflect
Require Import ssreflect eqtype ssrbool ssrfun seq.
From tlc.utility
Require Import seq.

Require Import comp flc.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section stack.

  Variable node : eqType.
  Variable message : eqType.

  Inductive stack : Type -> Type -> Type :=
  | Stack IR OI scs :
    comp node IR OI scs ->
    mapseq (fun x => stack (OR x) (II x)) scs ->
    stack IR OI
  | FairLossLink :
    stack (req_fl node message) (ind_fl node message).

End stack.
