Require Import mathcomp.ssreflect.seq.
Require Import mathcomp.ssreflect.ssreflect.
Require Import tlc.semantics.all_semantics.
Require Import tlc.syntax.all_syntax.
Require Import tlc.utility.partial_map.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Logical context of assertions *)
Definition context := seq assertion.

(* Produces a term equivalence map from a context
 * All premises of the form "tl = tr" appear in the equivalence map
 *)
Fixpoint context_equivalences (Gamma : context) : equivalents :=
  match Gamma with
  | [::] => [::]
  | A :: Gamma =>
    let e := context_equivalences Gamma in
    if A is APredicate (PEqual tl tr) then e{= tl := tr} else e
  end.
