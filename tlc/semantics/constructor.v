(* TLC in Coq
 *
 * Module: tlc.semantics.constructor
 * Purpose: Contains the semantics for constructors.
 *)

Require Import mathcomp.ssreflect.ssreflect.
Require Import mathcomp.ssreflect.ssrnat.
Require Import tlc.syntax.constructor.

(* Determine the arity of a constructor *)
Definition constructor_arity c :=
  match c with
  (* Unit *)
  | CUnit => 0
  (* Maybe *)
  | CNone => 0
  | CSome => 1
  (* Either *)
  | CLeft => 1
  | CRight => 1
  (* Pair *)
  | CPair => 2
  (* Boolean *)
  | CFalse => 0
  | CTrue => 0
  (* Natural *)
  | CZero => 0
  | CSucc => 1
  (* List *)
  | CNil => 0
  | CCons => 2
  (* Orientation *)
  | CRequest => 0
  | CIndication => 0
  | CPeriodic => 0
  (* PeriodicEvent *)
  | CPE => 0
  (* FLRequest *)
  | CFLSend => 2
  (* FLIndication *)
  | CFLDeliver => 2
  (* SLRequest *)
  | CSLSend => 2
  (* SLIndication *)
  | CSLDeliver => 2
  (* PLRequest *)
  | CPLSend => 2
  (* PLIndication *)
  | CPLDeliver => 2
  end.
