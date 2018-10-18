From mathcomp.ssreflect
Require Import ssreflect.
From tlc.assert
Require Import type rigid_var term prop lib interleavable_prop.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Inductive top_prop {C} : @prop C -> Type :=
| TPCorrect t :
  top_prop (Atom (App TLC.correct t))
| TPRequestEv n e :
  top_prop (TLC.IsOn n (TLC.IsEvent TLC.nil TLC.Request e))
| TPIndicationEv n e i :
  top_prop (TLC.IsOn n
    (TLC.IsEvent (App (App TLC.cons i) TLC.nil) TLC.Indication e))
| TPPeriodicEv n e :
  top_prop (TLC.IsOn n (TLC.IsEvent TLC.nil TLC.Periodic e))
| TPNot p :
  top_prop p ->
  top_prop (Not p)
| TPOr p q :
  top_prop p ->
  top_prop q ->
  top_prop (Or p q)
| TPForall t (x : rigid_var t) p :
  top_prop p ->
  top_prop (Forall x p)
| TPUntil' p q :
  p <> Atom (@Const _ Bool false) ->
  top_prop p ->
  top_prop q ->
  top_prop (Until' p q)
| TPSince' p q :
  p <> Atom (@Const _ Bool false) ->
  top_prop p ->
  top_prop q ->
  top_prop (Since' p q).

Lemma top_prop_is_interleavable {C} p (TP : @top_prop C p)
: interleavable_prop p.
Proof.
  elim: TP; try by constructor;
  try by (rewrite /TLC.IsOn /TLC.IsEvent /TLC.Eq; repeat constructor).
Qed.
