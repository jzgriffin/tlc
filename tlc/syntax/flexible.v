(* TLC in Coq
 *
 * Module: tlc.syntax.flexible
 * Purpose: Contains the syntax of flexible variables.
 *)

From HB Require Import structures.
Require Import mathcomp.ssreflect.eqtype.
Require Import mathcomp.ssreflect.ssrbool.
Require Import mathcomp.ssreflect.ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Type of flexible variables
 * Flexible variables may assume distinct values in different elements of a
 * trace.
 *)
Inductive flexible :=
| Fn (* Identifier of the node that executes the event *)
| Fr (* Round number that executes the event *)
| Fd (* Location identifier that the event is executed at *)
| Fo (* Orientation of the event *)
| Fe (* User event that is processed *)
| Fors (* Output requests that the event issues *)
| Fois (* Output indications that the event issues *)
| Fs (* Pre-state of the event *)
| Fs'. (* Post-state of the event *)

(* Equality *)
Section eq.

  (* Boolean equality *)
  Definition flexible_eq x1 x2 :=
    match x1, x2 with
    | Fn, Fn => true
    | Fr, Fr => true
    | Fd, Fd => true
    | Fo, Fo => true
    | Fe, Fe => true
    | Fors, Fors => true
    | Fois, Fois => true
    | Fs, Fs => true
    | Fs', Fs' => true
    | _, _ => false
    end.

  (* Boolean equality reflection *)
  Lemma flexible_eqP : Equality.axiom flexible_eq.
  Proof.
    by case; case; constructor.
  Qed.

  (* EqType canonical structures *)
  HB.instance Definition _ := hasDecEq.Build flexible flexible_eqP.

End eq.
