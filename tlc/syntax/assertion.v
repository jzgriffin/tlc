Require Import mathcomp.ssreflect.eqtype.
Require Import mathcomp.ssreflect.ssrbool.
Require Import mathcomp.ssreflect.ssreflect.
Require Import tlc.operation.orientation.
Require Import tlc.syntax.constructor.
Require Import tlc.syntax.literal.
Require Import tlc.syntax.parameter.
Require Import tlc.syntax.predicate.
Require Import tlc.syntax.term.
Require Import tlc.syntax.variable.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Forms of logical assertions *)
Inductive assertion :=
| APredicate (p : predicate)
| ANot (A : assertion)
| AAnd (Al Ar : assertion)
| AForAll (v : variable) (A : assertion)
| AAlways' (A : assertion)
| AAlwaysP' (A : assertion)
| AEventually' (A : assertion)
| AEventuallyP' (A : assertion)
| ANext (A : assertion)
| APrevious (A : assertion)
| ASelf (A : assertion).

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
  Canonical Structure assertion_eqMixin := EqMixin assertion_eqP.
  Canonical Structure assertion_eqType :=
    Eval hnf in EqType assertion assertion_eqMixin.

End eq.

(* Notation scope *)
Bind Scope assertion_scope with assertion.
Delimit Scope assertion_scope with assertion.
Notation "{A: A }" := (A%assertion)
  (at level 0, A at level 100, no associativity, only parsing).

(* Constructor notations *)
Notation "# p" := (APredicate p) : assertion_scope.
Notation "~ A" := (ANot A) : assertion_scope.
Notation "Al /\ Ar" := (AAnd Al Ar) : assertion_scope.
Notation "forall: v , A" := (AForAll v A)
  (at level 65, v at level 99, A at level 200, right associativity)
  : assertion_scope.
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
Definition AFalse := {A: # PFalse}.
Definition AEqual tl tr := {A: # (PEqual tl tr)}.
Notation "tl = tr" := (AEqual tl tr) : assertion_scope.
Definition AIn t ts := {A: # (PIn t ts)}.
Notation "t \in ts" := (AIn t ts) : assertion_scope.
Definition ACorrect tn := {A: # (PCorrect tn)}.
Notation "'correct' tn" := (ACorrect tn)
  (at level 0, no associativity) : assertion_scope.

(* Derived propositional operators *)
Definition AOr Al Ar := {A: ~(~Al /\ ~Ar)}.
Notation "Al \/ Ar" := (AOr Al Ar) : assertion_scope.
Definition AIf Al Ar := {A: ~Al \/ Ar}.
Notation "Al -> Ar" := (AIf Al Ar) : assertion_scope.
Definition AIff Al Ar := {A: (Al -> Ar) /\ (Ar -> Al)}.
Notation "Al <-> Ar" := (AIff Al Ar) : assertion_scope.
Definition AExists v A := {A: ~forall: v, ~A}.
Notation "exists: v , A" := (AExists v A)
  (at level 65, v at level 99, A at level 200, right associativity)
  : assertion_scope.

(* Derived strict and immediate past temporal operators *)
Definition APrevious' A := {A: ~previous ~A}.
Notation "previous^ A" := (APrevious' A)
  (at level 60, right associativity) : assertion_scope.

(* Derived reflexive future temporal operators *)
Definition AEventually A := {A: A \/ eventually^ A}.
Notation "'eventually' A" := (AEventually A)
  (at level 60, right associativity) : assertion_scope.
Definition AAlways A := {A: A /\ always^ A}.
Notation "'always' A" := (AAlways A)
  (at level 60, right associativity) : assertion_scope.

(* Derived reflexive past temporal operators *)
Definition AEventuallyP A := {A: A \/ eventuallyp^ A}.
Notation "'eventuallyp' A" := (AEventuallyP A)
  (at level 60, right associativity) : assertion_scope.
Definition AAlwaysP A := {A: A /\ alwaysp^ A}.
Notation "'alwaysp' A" := (AAlwaysP A)
  (at level 60, right associativity) : assertion_scope.

(* Additional temporal operators *)
Definition AEntails Al Ar := {A: always (Al -> Ar)}.
Notation "Al =>> Ar" := (AEntails Al Ar)
  (at level 99, right associativity) : assertion_scope.
Definition ACongruent Al Ar := {A: (Al =>> Ar) /\ (Ar =>> Al)}.
Notation "Al <=> Ar" := (ACongruent Al Ar)
  (at level 95, no associativity) : assertion_scope.
Definition AFollowedBy Al Ar := {A: Al =>> eventually Ar}.
Notation "Al ~> Ar" := (AFollowedBy Al Ar)
  (at level 90, right associativity) : assertion_scope.
Definition APrecededBy Al Ar := {A: Al =>> eventuallyp Ar}.
Notation "Al <~ Ar" := (APrecededBy Al Ar)
  (at level 90, right associativity) : assertion_scope.

(* Component syntactic sugar *)
Definition AWhenOn tn A := {A: "Fn" = tn /\ A}.
Notation "when-on[ tn ] A" := (AWhenOn tn A)
  (at level 60, right associativity) : assertion_scope.
Definition AWhenTopRequest te :=
  {A: "Fd" = [] /\ "Fo" = ORequest /\ "Fe" = te}.
Notation "when[]-> te" := (AWhenTopRequest te)
  (at level 60, no associativity) : assertion_scope.
Definition AWhenTopIndication te :=
  {A: "Fd" = [] /\ "Fo" = OIndication /\ "Fe" = te}.
Notation "when[]<- te" := (AWhenTopIndication te)
  (at level 60, no associativity) : assertion_scope.
Definition AWhenTopPeriodic te :=
  {A: "Fd" = [] /\ "Fo" = OPeriodic /\ "Fe" = te}.
Notation "when[]~> te" := (AWhenTopPeriodic te)
  (at level 60, no associativity) : assertion_scope.
Definition AWhenSubRequest ti te :=
  {A: "Fd" = [ti] /\ "Fo" = ORequest /\ "Fe" = te}.
Notation "when[ ti ]-> te" := (AWhenSubRequest ti te)
  (at level 60, no associativity) : assertion_scope.
Definition AWhenSubIndication ti te :=
  {A: "Fd" = [ti] /\ "Fo" = OIndication /\ "Fe" = te}.
Notation "when[ ti ]<- te" := (AWhenSubIndication ti te)
  (at level 60, no associativity) : assertion_scope.
Definition AWhenSubPeriodic ti te :=
  {A: "Fd" = [ti] /\ "Fo" = OPeriodic /\ "Fe" = te}.
Notation "when[ ti ]~> te" := (AWhenSubPeriodic ti te)
  (at level 60, no associativity) : assertion_scope.
Definition AWhenSelf :=
  {A: (exists: "i", "Fd" = ["i"] /\ "Fo" = OIndication) \/
    ("Fd" = [] /\ "Fo" = ORequest) \/
    ("Fd" = [] /\ "Fo" = OPeriodic)}.
Notation "when-self" := (AWhenSelf)
  (at level 60, no associativity) : assertion_scope.

(* Derived predicate notations *)
Definition ATrue := {A: ~AFalse}.
Definition ANotEqual tl tr := {A: ~(tl = tr)}.
Notation "tl <> tr" := (ANotEqual tl tr) : assertion_scope.
Definition ANotIn t ts := {A: ~(t \in ts)}.
Notation "t \notin ts" := (ANotIn t ts) : assertion_scope.

(* Proposition for non-temporal assertions *)
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
  non_temporal_assertion {A: forall: v, A}.

Definition non_temporal_assertion_t :=
  {A : assertion & non_temporal_assertion A}.
