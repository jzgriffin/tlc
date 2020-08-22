(* TLC in Coq
 *
 * Module: tlc.utility.ascii
 * Purpose: Contains the equality type for ASCII characters.
 *)

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
  Definition ascii_eqMixin := EqMixin Ascii.eqb_spec.
  Canonical ascii_eqType := EqType ascii ascii_eqMixin.

End eq.
