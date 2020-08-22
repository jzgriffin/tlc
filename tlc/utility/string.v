(* TLC in Coq
 *
 * Module: tlc.utility.string
 * Purpose: Contains the equality type for ASCII strings.
 *)

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
  Definition string_eqMixin := EqMixin String.eqb_spec.
  Canonical string_eqType := EqType string string_eqMixin.

End eq.
