(* TLC in Coq
 *
 * Module: tlc.syntax.assertion
 * Purpose: Contains the syntax of assertions.
 *)

Require Import mathcomp.ssreflect.eqtype.
Require Import mathcomp.ssreflect.seq.
Require Import mathcomp.ssreflect.ssrbool.
Require Import mathcomp.ssreflect.ssreflect.
Require Import mathcomp.ssreflect.ssrnat.
Require Import tlc.operation.orientation.
Require Import tlc.syntax.constructor.
Require Import tlc.syntax.literal.
Require Import tlc.syntax.parameter.
Require Import tlc.syntax.predicate.
Require Import tlc.syntax.term.
Require Import tlc.syntax.variable.
Require Import tlc.utility.seq.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Forms of logical assertions *)
Inductive assertion :=
(* First-order logic *)
| APredicate (p : predicate) (* Predicates *)
| ANot (A : assertion) (* Negation *)
| AAnd (Al Ar : assertion) (* Conjunction *)
| AForAll (v : variable) (A : assertion) (* Universal quantification *)
(* Temporal logic *)
| AAlways' (A : assertion) (* Always strictly in the future *)
| AAlwaysP' (A : assertion) (* Always strictly in the past *)
| AEventually' (A : assertion) (* Eventually strictly in the future *)
| AEventuallyP' (A : assertion) (* Eventually strictly in the past *)
| ANext (A : assertion) (* In the next label *)
| APrevious (A : assertion) (* In the previous label *)
| ASelf (A : assertion). (* Subtrace of self events *)

(* Equality *)
Section eq.

  (* Boolean equality *)
  Fixpoint assertion_eq Al Ar :=
    match Al, Ar with
    | APredicate pl, APredicate pr => pl == pr
    | APredicate _, _ => false
    | ANot Al, ANot Ar => assertion_eq Al Ar
    | ANot _, _ => false
    | AAnd All Arl, AAnd Alr Arr =>
      assertion_eq All Alr && assertion_eq Arl Arr
    | AAnd _ _, _ => false
    | AForAll vl Al, AForAll vr Ar =>
      (vl == vr) && assertion_eq Al Ar
    | AForAll _ _, _ => false
    | AAlways' Al, AAlways' Ar => assertion_eq Al Ar
    | AAlways' _, _ => false
    | AAlwaysP' Al, AAlwaysP' Ar => assertion_eq Al Ar
    | AAlwaysP' _, _ => false
    | AEventually' Al, AEventually' Ar => assertion_eq Al Ar
    | AEventually' _, _ => false
    | AEventuallyP' Al, AEventuallyP' Ar => assertion_eq Al Ar
    | AEventuallyP' _, _ => false
    | ANext Al, ANext Ar => assertion_eq Al Ar
    | ANext _, _ => false
    | APrevious Al, APrevious Ar => assertion_eq Al Ar
    | APrevious _, _ => false
    | ASelf Al, ASelf Ar => assertion_eq Al Ar
    | ASelf _, _ => false
    end.

  (* Boolean equality reflection *)
  Lemma assertion_eqP : Equality.axiom assertion_eq.
  Proof.
    elim=> [pl | Al IHA | All IHAl Arl IHAr | vl Al IHA | Al IHA | Al IHA
      | Al IHA | Al IHA | Al IHA | Al IHA | Al IHA]
      [pr | Ar | Alr Arr | vr Ar | Ar | Ar | Ar | Ar | Ar | Ar | Ar] //=;
      try by constructor.
    - case H: (pl == pr); move/eqP: H => H //=; subst;
        last by constructor; move=> [].
      by constructor.
    - case H: (assertion_eq Al Ar); move/IHA: H => H //=; subst;
        last by constructor; move=> [].
      by constructor.
    - case H: (assertion_eq All Alr); move/IHAl: H => H //=; subst;
        last by constructor; move=> [].
      case H: (assertion_eq Arl Arr); move/IHAr: H => H //=; subst;
        last by constructor; move=> [].
      by constructor.
    - case H: (vl == vr); move/eqP: H => H //=; subst;
        last by constructor; move=> [].
      case H: (assertion_eq Al Ar); move/IHA: H => H //=; subst;
        last by constructor; move=> [].
      by constructor.
    - case H: (assertion_eq Al Ar); move/IHA: H => H //=; subst;
        last by constructor; move=> [].
      by constructor.
    - case H: (assertion_eq Al Ar); move/IHA: H => H //=; subst;
        last by constructor; move=> [].
      by constructor.
    - case H: (assertion_eq Al Ar); move/IHA: H => H //=; subst;
        last by constructor; move=> [].
      by constructor.
    - case H: (assertion_eq Al Ar); move/IHA: H => H //=; subst;
        last by constructor; move=> [].
      by constructor.
    - case H: (assertion_eq Al Ar); move/IHA: H => H //=; subst;
        last by constructor; move=> [].
      by constructor.
    - case H: (assertion_eq Al Ar); move/IHA: H => H //=; subst;
        last by constructor; move=> [].
      by constructor.
    - case H: (assertion_eq Al Ar); move/IHA: H => H //=; subst;
        last by constructor; move=> [].
      by constructor.
  Qed.

  (* EqType canonical structures *)
  Canonical Structure assertion_eqMixin :=
    Eval hnf in EqMixin assertion_eqP.
  Canonical Structure assertion_eqType :=
    Eval hnf in EqType assertion assertion_eqMixin.

End eq.

(* Notation scope *)
Bind Scope assertion_scope with assertion.
Delimit Scope assertion_scope with assertion.
Notation "{A: A }" := (A%assertion)
  (at level 0, A at level 100, no associativity, only parsing).

(* Constructor notations *)
Notation "# p" := (APredicate p)
  (at level 0, no associativity, format "'#' p") : assertion_scope.
Notation "~ A" := (ANot A) : assertion_scope.
Notation "Al /\ Ar" := (AAnd Al Ar) : assertion_scope.
Notation "forall: v1 , .. , vn : A" := (AForAll v1 (.. (AForAll vn A) ..))
  (at level 65, v1 at level 99, vn at level 99, A at level 200,
    right associativity) : assertion_scope.
Notation "always^ A" := (AAlways' A)
  (at level 60, right associativity) : assertion_scope.
Notation "alwaysp^ A" := (AAlwaysP' A)
  (at level 60, right associativity) : assertion_scope.
Notation "eventually^ A" := (AEventually' A)
  (at level 60, right associativity) : assertion_scope.
Notation "eventuallyp^ A" := (AEventuallyP' A)
  (at level 60, right associativity) : assertion_scope.
Notation "'next' A" := (ANext A)
  (at level 60, right associativity) : assertion_scope.
Notation "'previous' A" := (APrevious A)
  (at level 60, right associativity) : assertion_scope.
Notation "'self' A" := (ASelf A)
  (at level 60, right associativity) : assertion_scope.

(* Predicate notations *)
Notation AFalse := {A: # PFalse}.
Notation AEqual tl tr := {A: # (PEqual tl tr)}.
Notation "tl = tr" := (AEqual tl tr) : assertion_scope.
Notation AIn t ts := {A: # (PIn t ts)}.
Notation "t \in ts" := (AIn t ts) : assertion_scope.
Notation AExtension ts' ts := {A: # (PExtension ts' ts)}.
Notation "ts' <<< ts" := (AExtension ts' ts)
  (at level 20, no associativity) : assertion_scope.
Notation ACorrect tn := {A: # (PCorrect tn)}.
Notation "'correct' tn" := (ACorrect tn)
  (at level 0, no associativity) : assertion_scope.
Notation AGe tl tr := {A: # (PGe tl tr)}.
Notation "tl >= tr" := (AGe tl tr) : assertion_scope.
Notation ALe tl tr := {A: # (PLe tl tr)}.
Notation "tl <= tr" := (ALe tl tr) : assertion_scope.

(* Derived first-order operators *)
Notation AOr Al Ar := {A: ~(~Al /\ ~Ar)}.
Notation "Al \/ Ar" := (AOr Al Ar) : assertion_scope.
Notation AIf Al Ar := {A: ~Al \/ Ar}.
Notation "Al -> Ar" := (AIf Al Ar) : assertion_scope.
Notation AIff Al Ar := {A: (Al -> Ar) /\ (Ar -> Al)}.
Notation "Al <-> Ar" := (AIff Al Ar) : assertion_scope.
Notation AExists v A := {A: ~forall: v: ~A}.
Notation "exists: v : A" := (AExists v A)
  (at level 65, v at level 99, A at level 200, right associativity)
  : assertion_scope.

(* Derived strict and immediate past temporal operators *)
Notation APrevious' A := {A: ~previous ~A}.
Notation "previous^ A" := (APrevious' A)
  (at level 60, right associativity) : assertion_scope.

(* Derived reflexive future temporal operators *)
Notation AEventually A := {A: A \/ eventually^ A}.
Notation "'eventually' A" := (AEventually A)
  (at level 60, right associativity) : assertion_scope.
Notation AAlways A := {A: A /\ always^ A}.
Notation "'always' A" := (AAlways A)
  (at level 60, right associativity) : assertion_scope.

(* Derived reflexive past temporal operators *)
Notation AEventuallyP A := {A: A \/ eventuallyp^ A}.
Notation "'eventuallyp' A" := (AEventuallyP A)
  (at level 60, right associativity) : assertion_scope.
Notation AAlwaysP A := {A: A /\ alwaysp^ A}.
Notation "'alwaysp' A" := (AAlwaysP A)
  (at level 60, right associativity) : assertion_scope.

(* Additional temporal operators *)
Notation AEntails Al Ar := {A: always (Al -> Ar)}.
Notation "Al =>> Ar" := (AEntails Al Ar)
  (at level 99, right associativity) : assertion_scope.
Notation ACongruent Al Ar := {A: (Al =>> Ar) /\ (Ar =>> Al)}.
Notation "Al <=> Ar" := (ACongruent Al Ar)
  (at level 95, no associativity) : assertion_scope.
Notation AFollowedBy Al Ar := {A: Al =>> eventually Ar}.
Notation "Al ~> Ar" := (AFollowedBy Al Ar)
  (at level 90, right associativity) : assertion_scope.
Notation APrecededBy Al Ar := {A: Al =>> eventuallyp Ar}.
Notation "Al <~ Ar" := (APrecededBy Al Ar)
  (at level 90, right associativity) : assertion_scope.

(* Component syntactic sugar *)
Definition AOn tn A := {A: "Fn" = tn /\ A}.
Notation "'on' tn , A" := (AOn tn A)
  (at level 60, right associativity, format "'on'  tn ,  A")
  : assertion_scope.
Definition ATopRequest te :=
  {A: "Fd" = [] /\ "Fo" = ORequest /\ "Fe" = te}.
Notation "'event' []-> te" := (ATopRequest te)
  (at level 60, no associativity, format "'event'  []->  te")
  : assertion_scope.
Definition ATopIndication te :=
  {A: "Fd" = [] /\ "Fo" = OIndication /\ "Fe" = te}.
Notation "'event' []<- te" := (ATopIndication te)
  (at level 60, no associativity, format "'event'  []<-  te")
  : assertion_scope.
Definition ATopPeriodic te :=
  {A: "Fd" = [] /\ "Fo" = OPeriodic /\ "Fe" = te}.
Notation "'event' []~> te" := (ATopPeriodic te)
  (at level 60, no associativity, format "'event'  []~>  te")
  : assertion_scope.
Definition ASubRequest ti te :=
  {A: "Fd" = [ti] /\ "Fo" = ORequest /\ "Fe" = te}.
Notation "'event' [ ti ]-> te" := (ASubRequest ti te)
  (at level 60, no associativity, format "'event'  [ ti ]->  te")
  : assertion_scope.
Definition ASubIndication ti te :=
  {A: "Fd" = [ti] /\ "Fo" = OIndication /\ "Fe" = te}.
Notation "'event' [ ti ]<- te" := (ASubIndication ti te)
  (at level 60, no associativity, format "'event'  [ ti ]<-  te")
  : assertion_scope.
Definition ASubPeriodic ti te :=
  {A: "Fd" = [ti] /\ "Fo" = OPeriodic /\ "Fe" = te}.
Notation "'event' [ ti ]~> te" := (ASubPeriodic ti te)
  (at level 60, no associativity, format "'event'  [ ti ]~>  te")
  : assertion_scope.
Definition ASelfEvent :=
  {A: (exists: "i": "Fd" = ["i"] /\ "Fo" = OIndication) \/
    ("Fd" = [] /\ "Fo" = ORequest) \/
    ("Fd" = [] /\ "Fo" = OPeriodic)}.
Notation "self-event" := (ASelfEvent)
  (at level 60, no associativity) : assertion_scope.

(* Derived predicate notations *)
Definition ATrue := {A: ~AFalse}.
Definition ANotEqual tl tr := {A: ~(tl = tr)}.
Notation "tl <> tr" := (ANotEqual tl tr) : assertion_scope.
Definition ANotIn t ts := {A: ~(t \in ts)}.
Notation "t \notin ts" := (ANotIn t ts) : assertion_scope.

(* Forms of non-temporal assertions
 * Non-temporal assertions do not contain any temporal operators.
 *)
Inductive non_temporal_assertion : assertion -> Type :=
| NTAPredicate p :
  non_temporal_assertion {A: #p}
| NTANot A :
  non_temporal_assertion A ->
  non_temporal_assertion {A: ~A}
| NTAAnd Al Ar :
  non_temporal_assertion Al ->
  non_temporal_assertion Ar ->
  non_temporal_assertion {A: Al /\ Ar}
| NTAForAll v A :
  non_temporal_assertion A ->
  non_temporal_assertion {A: forall: v: A}.

(* Forms of assertions at a particular location
 * Location assertions are restricted to specific forms of atomic assertions
 * and any compositions of those assertions, excluding the next, previous, and
 * self operators.
 *
 * The sequence of naturals represents the distinct location at which the
 * assertion is made.
 *)
Inductive location_assertion : seq nat -> assertion -> Type :=
| LAEventOn d tn dp to te :
  location_assertion d {A: on tn,
    ("Fd" = (TList [seq TLiteral (LNatural i) | i <- dp ++ d]) /\
      "Fo" = to /\ "Fe" = te)}
| LACorrect d tn :
  location_assertion d {A: correct tn}
| LANot d A :
  location_assertion d A ->
  location_assertion d {A: ~A}
| LAAnd d Al Ar :
  location_assertion d Al ->
  location_assertion d Ar ->
  location_assertion d {A: Al /\ Ar}
| LAForAll d v A :
  location_assertion d A ->
  location_assertion d {A: forall: v: A}
| LAAlways' d A :
  location_assertion d A ->
  location_assertion d {A: always^ A}
| LAAlwaysP' d A :
  location_assertion d A ->
  location_assertion d {A: alwaysp^ A}
| LAEventually' d A :
  location_assertion d A ->
  location_assertion d {A: eventually^ A}
| LAEventuallyP' d A :
  location_assertion d A ->
  location_assertion d {A: eventuallyp^ A}.

(* Derived first-order operators *)
Lemma LAOr d Al Ar :
  location_assertion d Al ->
  location_assertion d Ar ->
  location_assertion d {A: Al \/ Ar}.
Proof. move=> LAl LAr; by repeat constructor. Defined.
Hint Resolve LAOr.

Lemma LAIf d Al Ar :
  location_assertion d Al ->
  location_assertion d Ar ->
  location_assertion d {A: Al -> Ar}.
Proof. move=> LAl LAr; by repeat constructor. Defined.
Hint Resolve LAIf.

Lemma LAIff d Al Ar :
  location_assertion d Al ->
  location_assertion d Ar ->
  location_assertion d {A: Al <-> Ar}.
Proof. move=> LAl LAr; by repeat constructor. Defined.
Hint Resolve LAIff.

Lemma LAExists d v A :
  location_assertion d A ->
  location_assertion d {A: exists: v: A}.
Proof. move=> LA; by repeat constructor. Qed.
Hint Resolve LAExists.

(* Derived reflexive future temporal operators *)
Lemma LAEventually d A :
  location_assertion d A ->
  location_assertion d {A: eventually A}.
Proof. move=> LA; by repeat constructor. Defined.
Hint Resolve LAEventually.

Lemma LAAlways d A :
  location_assertion d A ->
  location_assertion d {A: always A}.
Proof. move=> LA; by repeat constructor. Defined.
Hint Resolve LAAlways.

(* Derived reflexive past temporal operators *)
Lemma LAEventuallyP d A :
  location_assertion d A ->
  location_assertion d {A: eventuallyp A}.
Proof. move=> LA; by repeat constructor. Defined.
Hint Resolve LAEventuallyP.

Lemma LAAlwaysP d A :
  location_assertion d A ->
  location_assertion d {A: alwaysp A}.
Proof. move=> LA; by repeat constructor. Defined.
Hint Resolve LAAlwaysP.

(* Additional temporal operators *)
Lemma LAEntails d Al Ar :
  location_assertion d Al ->
  location_assertion d Ar ->
  location_assertion d {A: Al =>> Ar}.
Proof. move=> LAl LAr; by repeat constructor. Defined.
Hint Resolve LAEntails.

Lemma LACongruent d Al Ar :
  location_assertion d Al ->
  location_assertion d Ar ->
  location_assertion d {A: Al <=> Ar}.
Proof. move=> LAl LAr; by repeat constructor. Defined.
Hint Resolve LACongruent.

Lemma LAFollowedBy d Al Ar :
  location_assertion d Al ->
  location_assertion d Ar ->
  location_assertion d {A: Al ~> Ar}.
Proof. move=> LAl LAr; by repeat constructor. Defined.
Hint Resolve LAFollowedBy.

Lemma LAPrecededBy d Al Ar :
  location_assertion d Al ->
  location_assertion d Ar ->
  location_assertion d {A: Al <~ Ar}.
Proof. move=> LAl LAr; by repeat constructor. Defined.
Hint Resolve LAPrecededBy.

(* Forms of assertions on the top component
 * Top assertions are simply location assertions specialized for the empty
 * distinct location.
 *)
Definition top_assertion := location_assertion [::].

(* Forms of assertions that are invariants at a particular location
 * Location invariants are location assertions in which the outermost operator
 * is the always-in-the-future operator.
 *)
Inductive location_invariant : seq nat -> assertion -> Type :=
| LIA d A :
  location_assertion d A ->
  location_invariant d {A: always A}.

(* Every location invariant is also a location assertion *)
Lemma location_invariant_assertion d A :
  location_invariant d A ->
  location_assertion d A.
Proof.
  by case=> d' A' LA'; apply: LAAlways.
Defined.

(* Forms of assertions that are invariants on the top component
 * Top invariants are simply location invariants specialized for the empty
 * distinct location.
 *)
Definition top_invariant := location_invariant [::].

(* Forms of assertions that are self invariants
 * Self invariants are restricted to specific forms of atomic assertions and
 * any compositions of those assertions, excluding the next, previous, and
 * self operators.
 *
 * The sequence of naturals represents the distinct location at which the
 * assertion is made.
 *)
Inductive self_invariant : assertion -> Type :=
| SITopRequestOn tn te :
  self_invariant {A: on tn, event []-> te}
| SITopPeriodicOn tn te :
  self_invariant {A: on tn, event []~> te}
| SISubIndicationOn tn ti te :
  self_invariant {A: on tn, event [ti]<- te}
| SICorrect tn :
  self_invariant {A: correct tn}
| SINot A :
  self_invariant A ->
  self_invariant {A: ~A}
| SIAnd Al Ar :
  self_invariant Al ->
  self_invariant Ar ->
  self_invariant {A: Al /\ Ar}
| SIForAll v A :
  self_invariant A ->
  self_invariant {A: forall: v: A}
| SIAlways' A :
  self_invariant A ->
  self_invariant {A: always^ A}
| SIAlwaysP' A :
  self_invariant A ->
  self_invariant {A: alwaysp^ A}
| SIEventually' A :
  self_invariant A ->
  self_invariant {A: eventually^ A}
| SIEventuallyP' A :
  self_invariant A ->
  self_invariant {A: eventuallyp^ A}.
