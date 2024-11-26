(* TLC in Coq
 *
 * Module: tlc.utility.string
 * Purpose: Contains the equality type for ASCII strings.
 *)

From HB Require Import structures.
Require Import Coq.Strings.String.
Require Import mathcomp.ssreflect.eqtype.
Require Import mathcomp.ssreflect.ssrbool.
Require Import mathcomp.ssreflect.ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Equality *)
Section eq.

  (* EqType canonical structures *)
  HB.instance Definition _ := hasDecEq.Build string String.eqb_spec.

End eq.
