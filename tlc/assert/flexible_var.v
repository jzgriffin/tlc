From mathcomp.ssreflect
Require Import ssreflect eqtype ssrbool.
From tlc.utility
Require Import indeq.
From tlc.comp
Require Import component.
From tlc.assert
Require Import type.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Named flexible variables in the assertion language *)
Inductive flexible_var {C : component} : @type C -> Type :=
| Fn : flexible_var Node
| Fd : flexible_var Depth
| Fo : flexible_var Orientation
| Fe : flexible_var Event
| Fors : flexible_var [OREvent]
| Fois : flexible_var [OIEvent]
| Fs : flexible_var States
| Fs' : flexible_var States.

(* Equality *)
Section eq.

  Definition flexible_var_eq {C t} (x x' : @flexible_var C t) :=
    match x, x' with
    | Fn, Fn => true
    | Fd, Fd => true
    | Fo, Fo => true
    | Fe, Fe => true
    | Fors, Fors => true
    | Fois, Fois => true
    | Fs, Fs => true
    | Fs', Fs' => true
    | _, _ => false
    end.

  Lemma flexible_var_eqP {C t} : Equality.axiom (@flexible_var_eq C t).
  Proof.
    (* TODO *)
  Admitted.

  Canonical flexible_var_eqMixin {C t} :=
    EqMixin (@flexible_var_eqP C t).
  Canonical flexible_var_eqType {C t} :=
    Eval hnf in EqType (@flexible_var C t) (@flexible_var_eqMixin C t).

End eq.
