From mathcomp.ssreflect
Require Import ssreflect eqtype ssrbool ssrfun seq.
From tlc.utility
Require Import mapseq.
From tlc.comp
Require Import component flc.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Stack of components *)
Section stack.

  Inductive stack {N M : eqType} : eqType -> eqType -> Type :=
  | Stack C IR OI (Cs : seq component) :
    node C = N ->
    message C = M ->
    ir_event C = IR ->
    oi_event C = OI ->
    or_ii_events C = [seq (ir_event x, oi_event x) | x <- Cs] ->
    mapseq (fun x => stack (ir_event x) (oi_event x)) Cs ->
    stack IR OI
  | FairLossLink :
    stack (@req_fl N M) (@ind_fl N M).

End stack.
