(* TLC in Coq
 *
 * Module: tlc.utility.ascii
 * Purpose: Contains the equality type for ASCII characters.
 *)

From HB Require Import structures.
Require Import Coq.Strings.Ascii.
Require Import mathcomp.ssreflect.eqtype.
Require Import mathcomp.ssreflect.ssrbool.
Require Import mathcomp.ssreflect.ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Equality *)
Section eq.

  (* EqType canonical structures *)
  HB.instance Definition _ := hasDecEq.Build ascii Ascii.eqb_spec.

End eq.
