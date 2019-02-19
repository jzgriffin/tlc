Require Import mathcomp.ssreflect.eqtype.
Require Import mathcomp.ssreflect.ssrbool.
Require Import mathcomp.ssreflect.ssreflect.
Require Import tlc.syntax.term.
Require Import tlc.utility.partial_map.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Partial mapping of proposed equivalent terms *)
Definition equivalents := partial_map [eqType of term] term.
