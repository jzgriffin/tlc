(* TLC in Coq
 *
 * Module: tlc.logic.predicate
 * Purpose: Contains derived rules and lemmas regarding predicates.
 *)

Require Import mathcomp.ssreflect.seq.
Require Import mathcomp.ssreflect.ssrbool.
Require Import mathcomp.ssreflect.ssreflect.
Require Import tlc.logic.context.
Require Import tlc.logic.derives.
Require Import tlc.logic.sequent.
Require Import tlc.semantics.all_semantics.
Require Import tlc.syntax.all_syntax.
Require Import tlc.utility.result.
Require Import tlc.utility.seq.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Basic predicate lifting *)

(* Directly prove that x1 and x2 are equal *)
Lemma DPEqual C Delta x1 x2 :
  x1 = x2 ->
  Context Delta [::] ||- C, {-A x1 = x2 -}.
Proof.
Admitted.

(* Directly prove that x1 is less than x2 *)
Lemma DPLess C Delta x1 x1' x2 x2' :
  nat_of_term x1 = Some x1' ->
  nat_of_term x2 = Some x2' ->
  x1' < x2' ->
  Context Delta [::] ||- C, {-A x1 < x2 -}.
Proof.
Admitted.

(* Directly prove that y is a member of list xs *)
Lemma DPMember C Delta y xs xs' :
  list_of_term xs = Some xs' ->
  y \in xs' ->
  Context Delta [::] ||- C, {-A y \in xs -}.
Proof.
Admitted.

(* Directly prove that xs' is an extension of xs *)
Lemma DPExtension C Delta xs' xs'l xs xsl :
  list_of_term xs' = Some xs'l ->
  list_of_term xs = Some xsl ->
  extension xs'l xsl ->
  Context Delta [::] ||- C, {-A xs' <<< xs -}.
Proof.
Admitted.

(* Equality *)

(* FEqual reflects PEqual *)
Lemma DPEqualReflect C Delta :
  Context Delta [::] ||- C, {-A
    forall: forall: (* x1, x2 *)
    ($$1 == $$0) = true <->
    $$1 = $$0
  -}.
Proof.
Admitted.

(* Directly prove that x1 and x2 are not equal *)
Lemma DPNotEqual C Delta x1 x2 :
  x1 <> x2 ->
  Context Delta [::] ||- C, {-A x1 <> x2 -}.
Proof.
Admitted.

(* Equality is symmetric *)
Lemma DPEqualSymm C Delta :
  Context Delta [::] ||- C, {-A
    forall: forall: (* x1, x2 *)
    $$1 = $$0 <-> $$0 = $$1
  -}.
Proof.
  (* Used in PLC *)
Admitted.

(* Less than *)

(* Equality is a subset of less-than or equal *)
Lemma DPEqualLessEqual C Delta :
  Context Delta [::] ||- C, {-A
    forall: forall: (* x1, x2 *)
    $$1 = $$0 -> $$1 <= $$0
  -}.
Proof.
  (* Used in PLC *)
Admitted.

(* Equality is a subset of greater-than or equal *)
Lemma DPEqualGreaterEqual C Delta :
  Context Delta [::] ||- C, {-A
    forall: forall: (* x1, x2 *)
    $$1 = $$0 -> $$1 >= $$0
  -}.
Proof.
  (* Used in PLC *)
Admitted.

Lemma DPSuccGreaterEqual C Delta :
  Context Delta [::] ||- C, {-A
    forall: forall: (* x, y *)
    $$1 >= $$0 -> $$1.+1 >= $$0
  -}.
Proof.
Admitted.

Lemma DPGreaterEqual C Delta :
  Context Delta [::] ||- C, {-A
    forall: forall: (* x, y *)
    $$1 >= $$0 <-> $$1 = $$0 \/ $$1 > $$0
  -}.
Proof.
Admitted.

Lemma DPLessThanSucc C Delta :
  Context Delta [::] ||- C, {-A
    forall: (* x *)
    $$0 < $$0.+1
  -}.
Proof.
Admitted.

Lemma DPNotLessThanIfGreaterThan C Delta :
  Context Delta [::] ||- C, {-A
    forall: forall: (* x, y *)
    $$1 < $$0 ->
    ~($$1 > $$0)
  -}.
Proof.
Admitted.

(* Membership *)

(* FMember reflects PMember *)
Lemma DPMemberReflect C Delta :
  Context Delta [::] ||- C, {-A
    forall: forall: (* x, xs *)
    $$1 \in $$0 = true <->
    $$1 \in $$0
  -}.
Proof.
  (* Used in PLC *)
Admitted.

(* A member of a list appears at least once in that list *)
Lemma DPMemberCount C Delta :
  Context Delta [::] ||- C, {-A
    forall: forall: (* y, xs *)
    $$1 \in $$0 <->
    FCount ' $$1 ' $$0 >= 1
  -}.
Proof.
  (* Used in PLC *)
Admitted.

(* No element may appear in an empty list *)
Lemma DPMemberNil C Delta :
  Context Delta [::] ||- C, {-A
    forall: (* x *)
    ~ $$0 \in []
  -}.
Proof.
  (* Used in SLC & PLC *)
Admitted.
Ltac dpmembernilp :=
  match goal with
  | |- Context _ ({-A ?x \in [] -} :: _) ||- _, _ =>
    duse DPMemberNil; dforallp x; dnotp
  end.

(* Inductive definition of Member *)
Lemma DPMemberCons C Delta :
  Context Delta [::] ||- C, {-A
    forall: forall: forall: (* y, x, xs *)
    $$2 \in $$1 :: $$0 <->
    ($$2 = $$1 \/ $$2 \in $$0)
  -}.
Proof.
  (* Used in SLC *)
Admitted.

(* An element is always a member of a list containing only itself *)
Lemma DPMemberSingleton C Delta :
  Context Delta [::] ||- C, {-A
    forall: (* x *)
    $$0 \in [$$0]
  -}.
Proof.
  (* Used in SLC *)
Admitted.
Ltac dpmembersingletonp :=
  match goal with
  | |- Context _ ({-A ?x \in [?y] -} :: _) ||- _, _ =>
    duse DPMemberCons;
    dforallp x; dforallp y; dforallp {-t [] -};
    dsplitp; dswap; dclear; difp; first (by []);
    dorp; last (by dpmembernilp); dswap; dclear
  end.

(* Membership is closed under mapping *)
Lemma DPMemberMap C Delta :
  Context Delta [::] ||- C, {-A
    forall: forall: forall: (* f, xs, y *)
    $$0 \in $$1 <->
    ($$2 ' $$0) \in (FMap ' $$2 ' $$1)
  -}.
  Proof.
  (* Used in SLC *)
Admitted.

(* Membership is closed under concatenation *)
Lemma DPMemberConcat C Delta :
  Context Delta [::] ||- C, {-A
    forall: forall: forall: (* xs1, xs2, y *)
    $$0 \in $$2 \/ $$0 \in $$1 ->
    $$0 \in $$2 ++ $$1
  -}.
Proof.
  (* Used in SLC *)
Admitted.

(* An element is a member of a list iff a surrounding prefix/suffix pair exists *)
Lemma DPConcatMember C Delta :
  Context Delta [::] ||- C, {-A
    forall: forall: (* y, xs *)
    $$1 \in $$0 <->
    exists: exists: (* xs1, xs2 *)
    $$2 = $$1 ++ [$$3] ++ $$0
  -}.
Proof.
  (* Used in SLC & PLC *)
Admitted.

(* Membership is closed under set union *)
Lemma DPMemberSetUnion C Delta :
  Context Delta [::] ||- C, {-A
    forall: forall: forall: (* xs1, xs2, y *)
    $$0 \in $$2 \/ $$0 \in $$1 <->
    $$0 \in $$2 :|: $$1
  -}.
Proof.
  (* Used in SLC *)
Admitted.
Ltac dpmembersetunion :=
  match goal with
  | |- _ ||- _, {-A ?x \in ?y :|: ?z -} =>
    duse DPMemberSetUnion;
    dforallp y; dforallp z; dforallp x; dclean;
    dsplitp; dswap; dclear; difp; last by []
  end.

Lemma DPCountSingleton C Delta :
  Context Delta [::] ||- C, {-A
    forall: (* x *)
    FCount ' $$0 ' [$$0] = 1
  -}.
Proof.
Admitted.
