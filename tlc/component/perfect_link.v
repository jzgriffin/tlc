(* TLC in Coq
 *
 * Module: tlc.component.perfect_link
 * Purpose: Contains the functional implementation and logical specification
 * of the perfect link component.
 *)

Require Import mathcomp.ssreflect.eqtype.
Require Import mathcomp.ssreflect.seq.
Require Import mathcomp.ssreflect.ssrbool.
Require Import mathcomp.ssreflect.ssreflect.
Require Import tlc.component.component.
Require Import tlc.component.stubborn_link.
Require Import tlc.logic.all_logic.
Require Import tlc.semantics.all_semantics.
Require Import tlc.syntax.all_syntax.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Functional implementation *)
Definition perfect_link :=
  let slc := 0 in
  Component
  (* initialize *)
  {t: fun:
    (* Begin scoped parameters *)
    let n := {t: #(0, 0)} in
    (* End scoped parameters *)
    (0, [])
  }
  (* request *)
  {t: fun: fun: fun:
    (* Begin scoped parameters *)
    let n := {t: #(2, 0)} in
    let s := {t: #(1, 0)} in
    let ir := {t: #(0, 0)} in
    (* End scoped parameters *)
    let: (#, #) := s in: (* c, r *)
    (* Begin scoped parameters *)
    let n := {t: #(3, 0)} in
    let s := {t: #(2, 0)} in
    let ir := {t: #(1, 0)} in
    let c := {t: #(0, 0)} in
    let r := {t: #(0, 1)} in
    (* End scoped parameters *)
    match: ir with:
    {{ CPLSend $ # $ # (* n', m *) ->
      (* Begin scoped parameters *)
      let n := {t: #(4, 0)} in
      let s := {t: #(3, 0)} in
      let ir := {t: #(2, 0)} in
      let c := {t: #(1, 0)} in
      let r := {t: #(1, 1)} in
      let n' := {t: #(0, 0)} in
      let m := {t: #(0, 1)} in
      (* End scoped parameters *)
      let: # := c.+1 in: (* c' *)
      (* Begin scoped parameters *)
      let n := {t: #(5, 0)} in
      let s := {t: #(4, 0)} in
      let ir := {t: #(3, 0)} in
      let c := {t: #(2, 0)} in
      let r := {t: #(2, 1)} in
      let n' := {t: #(1, 0)} in
      let m := {t: #(1, 1)} in
      let c' := {t: #(0, 0)} in
      (* End scoped parameters *)
      let: # := (slc, CSLSend $ n' $ (c', m)) in: (* or *)
      (* Begin scoped parameters *)
      let n := {t: #(6, 0)} in
      let s := {t: #(5, 0)} in
      let ir := {t: #(4, 0)} in
      let c := {t: #(3, 0)} in
      let r := {t: #(3, 1)} in
      let n' := {t: #(2, 0)} in
      let m := {t: #(2, 1)} in
      let c' := {t: #(1, 0)} in
      let or := {t: #(0, 0)} in
      (* End scoped parameters *)
      ((c', r), [or], [])
    }} endmatch
  }
  (* indication *)
  {t: fun: fun: fun:
    (* Begin scoped parameters *)
    let n' := {t: #(2, 0)} in
    let s := {t: #(1, 0)} in
    let ii := {t: #(0, 0)} in
    (* End scoped parameters *)
    let: (#, #) := s in: (* c, r *)
    (* Begin scoped parameters *)
    let n' := {t: #(3, 0)} in
    let s := {t: #(2, 0)} in
    let ii := {t: #(1, 0)} in
    let c := {t: #(0, 0)} in
    let r := {t: #(0, 1)} in
    (* End scoped parameters *)
    match: #(1, 0) with:
    {{ (slc, CPLDeliver $ # $ (#, #)) (* n, c', m *) ->
      (* Begin scoped parameters *)
      let n' := {t: #(4, 0)} in
      let s := {t: #(3, 0)} in
      let ii := {t: #(2, 0)} in
      let c := {t: #(1, 0)} in
      let r := {t: #(1, 1)} in
      let n := {t: #(0, 0)} in
      let c' := {t: #(0, 1)} in
      let m := {t: #(0, 2)} in
      (* End scoped parameters *)
      if: (n, c') \in r
      then:
        (s, [], [])
      else:
        let: # := r \union [(n, c')] in: (* r' *)
        (* Begin scoped parameters *)
        let n' := {t: #(5, 0)} in
        let s := {t: #(4, 0)} in
        let ii := {t: #(3, 0)} in
        let c := {t: #(2, 0)} in
        let r := {t: #(2, 1)} in
        let n := {t: #(1, 0)} in
        let c' := {t: #(1, 1)} in
        let m := {t: #(1, 2)} in
        let r' := {t: #(0, 0)} in
        (* End scoped parameters *)
        let: # := CPLDeliver $ n $ m in: (* oi *)
        (* Begin scoped parameters *)
        let n' := {t: #(6, 0)} in
        let s := {t: #(5, 0)} in
        let ii := {t: #(4, 0)} in
        let c := {t: #(3, 0)} in
        let r := {t: #(3, 1)} in
        let n := {t: #(2, 0)} in
        let c' := {t: #(2, 1)} in
        let m := {t: #(2, 2)} in
        let r' := {t: #(1, 0)} in
        let oi := {t: #(0, 0)} in
        (* End scoped parameters *)
        ((c, r'), [], [oi])
    }} endmatch
  }
  (* periodic *)
  {t: fun: fun:
    (* Begin scoped parameters *)
    let n' := {t: #(1, 0)} in
    let s := {t: #(0, 0)} in
    (* End scoped parameters *)
    (s, [], [])
  }.

(* Specification *)

(* Reliable delivery
 * If a correct node n sends a message m to a correct node n', then n' will
 * eventually deliver m.
 *)
Theorem PL_1 : Context [::] [::] |- perfect_link, {A:
  correct "n" /\ correct "n'" ->
  (when-on["n"] when[]-> CPLSend $ "n'" $ "m" ~>
    when-on["n'"] when[]<- CPLDeliver $ "n" $ "m")
}.
Proof.
Admitted. (* TODO *)

(* No-duplication
 * If a message is sent at most once, it will be delivered at most once.
 *)
Theorem PL_2 : Context [::] [::] |- perfect_link, {A:
  (when-on["n'"] when[]-> CPLSend $ "n" $ "m" =>>
    alwaysp^ ~(when-on["n'"] when[]-> CPLSend $ "n" $ "m")) ->
  (when-on["n"] when[]<- CPLDeliver $ "n'" $ "m" =>>
    alwaysp^ ~(when-on["n"] when[]<- CPLDeliver $ "n'" $ "m"))
}.
Proof.
Admitted. (* TODO *)

(* No-forge
 * If a node n delivers a message m with sender n', then m was previously sent
 * to n by node n'.
 *)
Theorem PL_3 : Context [::] [::] |- perfect_link, {A:
  when-on["n"] when[]<- CPLDeliver $ "n'" $ "m" <~
  when-on["n'"] when[]-> CPLSend $ "n" $ "m"
}.
Proof.
Admitted. (* TODO *)
