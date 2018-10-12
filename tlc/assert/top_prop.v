From mathcomp.ssreflect
Require Import ssreflect.
From tlc.assert
Require Import rigid_var term prop lib interleavable_prop.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Inductive top_prop {C} : @prop C -> Type :=
| TACorrect t :
  top_prop (Atom (App TLC.correct t))
| TARequestEv n e :
  top_prop (TLC.On n (TLC.Ev TLC.nil TLC.Request e))
| TAIndicationEv n e i :
  top_prop (TLC.On n (TLC.Ev (App (App TLC.cons i) TLC.nil) TLC.Indication e))
| TAPeriodicEv n e :
  top_prop (TLC.On n (TLC.Ev TLC.nil TLC.Periodic e))
| TAConj A1 A2 :
  top_prop A1 ->
  top_prop A2 ->
  top_prop (Conj A1 A2)
| TANeg A0 :
  top_prop A0 ->
  top_prop (Neg A0)
| TAAlways t (x : rigid_var t) A0 :
  top_prop A0 ->
  top_prop (Always x A0)
| TAAlwaysF' A0 :
  top_prop A0 ->
  top_prop (AlwaysF' A0)
| TAAlwaysP' A0 :
  top_prop A0 ->
  top_prop (AlwaysP' A0)
| TAExistsF' A0 :
  top_prop A0 ->
  top_prop (ExistsF' A0)
| TAExistsP' A0 :
  top_prop A0 ->
  top_prop (ExistsP' A0).

Lemma top_prop_is_interleavable {C} A (TA : @top_prop C A) :
  interleavable_prop A.
Proof.
  elim: TA; try by constructor;
  try by (rewrite /TLC.On /TLC.Ev /TLC.Eq; repeat constructor).
Qed.
