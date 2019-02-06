Require Import mathcomp.ssreflect.eqtype.
Require Import mathcomp.ssreflect.ssrbool.
Require Import mathcomp.ssreflect.ssreflect.
Require Import tlc.syntax.parameter.
Require Import tlc.syntax.term.
Require Import tlc.syntax.variable.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Forms of logical assertions *)
Inductive assertion :=
| APredicate (t : term)
| ANot (A : assertion)
| AOr (Al Ar : assertion)
| AForAll (v : variable) (A : assertion)
| AUntil' (Al Ar : assertion)
| ASince' (Al Ar : assertion)
| ASelf (A : assertion).

(* Equality *)
Section eq.

  (* Boolean equality *)
  Fixpoint assertion_eq Al Ar :=
    match Al, Ar with
    | APredicate tl, APredicate tr => tl == tr
    | APredicate _, _ => false
    | ANot Al, ANot Ar => assertion_eq Al Ar
    | ANot _, _ => false
    | AOr All Arl, AOr Alr Arr =>
      assertion_eq All Alr && assertion_eq Arl Arr
    | AOr _ _, _ => false
    | AForAll vl Al, AForAll vr Ar =>
      (vl == vr) && assertion_eq Al Ar
    | AForAll _ _, _ => false
    | AUntil' All Arl, AUntil' Alr Arr =>
      assertion_eq All Alr && assertion_eq Arl Arr
    | AUntil' _ _, _ => false
    | ASince' All Arl, ASince' Alr Arr =>
      assertion_eq All Alr && assertion_eq Arl Arr
    | ASince' _ _, _ => false
    | ASelf Al, ASelf Ar => assertion_eq Al Ar
    | ASelf _, _ => false
    end.

  (* Boolean equality reflection *)
  Lemma assertion_eqP : Equality.axiom assertion_eq.
  Proof.
    elim=> [tl | Al IHA | All IHAl Arl IHAr | vl Al IHA | All IHAl Arl IHAr
      | All IHAl Arl IHAr | Al IHA] [tr | Ar | Alr Arr | vr Ar | Alr Arr
      | Alr Arr | Ar] //=; try by constructor.
    - case H: (tl == tr); move/eqP: H => H //=; subst;
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
    - case H: (assertion_eq All Alr); move/IHAl: H => H //=; subst;
        last by constructor; move=> [].
      case H: (assertion_eq Arl Arr); move/IHAr: H => H //=; subst;
        last by constructor; move=> [].
      by constructor.
    - case H: (assertion_eq All Alr); move/IHAl: H => H //=; subst;
        last by constructor; move=> [].
      case H: (assertion_eq Arl Arr); move/IHAr: H => H //=; subst;
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

(* Constructor coercions *)
Coercion APredicate : term >-> assertion.

(* Notation scope *)
Bind Scope assertion_scope with assertion.
Delimit Scope assertion_scope with assertion.
Notation "{A: A }" := (A%assertion)
  (at level 0, A at level 100, no associativity, only parsing).

(* Constructor notations *)
Notation "# t" := (APredicate t)
  (at level 0, no associativity, format "'#' t") : assertion_scope.
Notation "~ A" := (ANot A) : assertion_scope.
Notation "Al \/ Ar" := (AOr Al Ar) : assertion_scope.
Notation "forall: v , A" := (AForAll v A)
  (at level 65, v at level 99, A at level 200, right associativity)
  : assertion_scope.
Notation "Al until^ Ar" := (AUntil' Al Ar)
  (at level 60, right associativity) : assertion_scope.
Notation "Al since^ Ar" := (ASince' Al Ar)
  (at level 60, right associativity) : assertion_scope.
Notation "'self' A" := (ASelf A)
  (at level 60, right associativity) : assertion_scope.

(* Derived propositional operators *)
Definition AAnd Al Ar := {A: ~(~Al \/ ~Ar)}.
Notation "Al /\ Ar" := (AAnd Al Ar) : assertion_scope.
Definition AIf Al Ar := {A: ~Al \/ Ar}.
Notation "Al -> Ar" := (AIf Al Ar) : assertion_scope.
Definition AIff Al Ar := {A: (Al -> Ar) /\ (Ar -> Al)}.
Notation "Al <-> Ar" := (AIff Al Ar) : assertion_scope.
Definition AExists v A := {A: ~forall: v, ~A}.
Notation "exists: v , A" := (AExists v A)
  (at level 65, v at level 99, A at level 200, right associativity)
  : assertion_scope.

(* Derived strict and immediate future temporal operators *)
Definition AEventually' A := {A: true until^ A}.
Notation "eventually^ A" := (AEventually' A)
  (at level 60, right associativity) : assertion_scope.
Definition AAlways' A := {A: ~eventually^ ~A}.
Notation "always^ A" := (AAlways' A)
  (at level 60, right associativity) : assertion_scope.
Definition AUnless' Al Ar := {A: always^ Al \/ (Al until^ Ar)}.
Notation "Al unless^ Ar" := (AUnless' Al Ar)
  (at level 60, right associativity) : assertion_scope.
Definition ANext A := {A: false until^ A}.
Notation "'next' A" := (ANext A)
  (at level 60, right associativity) : assertion_scope.

(* Derived strict and immediate past temporal operators *)
Definition AEventuallyP' A := {A: true since^ A}.
Notation "eventuallyp^ A" := (AEventuallyP' A)
  (at level 60, right associativity) : assertion_scope.
Definition AAlwaysP' A := {A: ~eventuallyp^ ~A}.
Notation "alwaysp^ A" := (AAlwaysP' A)
  (at level 60, right associativity) : assertion_scope.
Definition ABackTo' Al Ar := {A: alwaysp^ Al \/ (Al since^ Ar)}.
Notation "Al backto^ Ar" := (ABackTo' Al Ar)
  (at level 60, right associativity) : assertion_scope.
Definition APrevious A := {A: false since^ A}.
Notation "'previous' A" := (APrevious A)
  (at level 60, right associativity) : assertion_scope.
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
Definition AUntil Al Ar := {A: Ar \/ (Al /\ (Al until^ Ar))}.
Notation "Al 'until' Ar" := (AUntil Al Ar)
  (at level 60, right associativity) : assertion_scope.
Definition AUnless Al Ar := {A: Ar \/ (Al /\ (Al unless^ Ar))}.
Notation "Al 'unless' Ar" := (AUnless Al Ar)
  (at level 60, right associativity) : assertion_scope.

(* Derived reflexive past temporal operators *)
Definition AEventuallyP A := {A: A \/ eventuallyp^ A}.
Notation "'eventuallyp' A" := (AEventuallyP A)
  (at level 60, right associativity) : assertion_scope.
Definition AAlwaysP A := {A: A /\ alwaysp^ A}.
Notation "'alwaysp' A" := (AAlwaysP A)
  (at level 60, right associativity) : assertion_scope.
Definition ASince Al Ar := {A: Ar \/ (Al /\ (Al since^ Ar))}.
Notation "Al 'since' Ar" := (ASince Al Ar)
  (at level 60, right associativity) : assertion_scope.
Definition ABackTo Al Ar := {A: Ar \/ (Al /\ (Al backto^ Ar))}.
Notation "Al 'backto' Ar" := (ABackTo Al Ar)
  (at level 60, right associativity) : assertion_scope.

(* Additional temporal operators *)
Definition AEntails Al Ar := {A: always (Al -> Ar)}.
Notation "Al =>> Ar" := (AEntails Al Ar)
  (at level 99, right associativity) : assertion_scope.
Definition ACongruent Al Ar := {A: (Al =>> Ar) /\ (Ar =>> Al)}.
Notation "Al <=> Ar" := (ACongruent Al Ar)
  (at level 95, no associativity) : assertion_scope.
Definition ALeadsTo Al Ar := {A: Al =>> eventually Ar}.
Notation "Al ~> Ar" := (ALeadsTo Al Ar)
  (at level 90, right associativity) : assertion_scope.
Definition APrecededBy Al Ar := {A: Al =>> eventuallyp Ar}.
Notation "Al <~ Ar" := (APrecededBy Al Ar)
  (at level 90, right associativity) : assertion_scope.
