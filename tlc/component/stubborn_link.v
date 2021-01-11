(* TLC in Coq
 *
 * Module: tlc.component.stubborn_link
 * Purpose: Contains the functional implementation of the stubborn link component.
 *)

Require Import mathcomp.ssreflect.ssrbool.
Require Import mathcomp.ssreflect.ssreflect.
Require Import tlc.component.component.
Require Import tlc.semantics.all_semantics.
Require Import tlc.syntax.all_syntax.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Functional implementation *)
Definition stubborn_link :=
  let flc := 0 in
  let initialize :=
    {-t fun: (* n *)
      []
    -} in
  let request :=
    {-t fun: fun: fun: (* n, s, ir *)
      match: $$0 with:
      { CSLSend ' $0 ' $1 (* {n', m} *) ->
        ($$2 :|: [($0, $1)], [(term_of_nat flc, CFLSend ' $0 ' $1)], [])
      }
    -} in
  let indication :=
    {-t fun: fun: fun: (* n, s, ii *)
      match: $$0 with:
      { (pattern_of_nat flc, CFLDeliver ' $0 ' $1) (* {n, m} *) ->
        ($$2, [], [CSLDeliver ' $0 ' $1])
      }
    -} in
  let periodic :=
    {-t fun: fun: (* n, s *)
      ($$0, (fun: (* (n', m) *)
        (term_of_nat flc, CFLSend ' ($$0).1 ' ($$0).2)) <$> $$0, [])
    -} in
  Component
    (Logic.eq_refl : term_computable initialize)
    (Logic.eq_refl : term_computable request)
    (Logic.eq_refl : term_computable indication)
    (Logic.eq_refl : term_computable periodic).
