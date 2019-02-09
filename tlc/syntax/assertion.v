Require Import mathcomp.ssreflect.eqtype.
Require Import mathcomp.ssreflect.ssrbool.
Require Import mathcomp.ssreflect.ssreflect.
Require Import tlc.syntax.constructor.
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
    | APredicate pl, APredicate pr => pl == pr
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
    elim=> [pl | Al IHA | All IHAl Arl IHAr | vl Al IHA | All IHAl Arl IHAr
      | All IHAl Arl IHAr | Al IHA] [pr | Ar | Alr Arr | vr Ar | Alr Arr
      | Alr Arr | Ar] //=; try by constructor.
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

(* Notation scope *)
Bind Scope assertion_scope with assertion.
Delimit Scope assertion_scope with assertion.
Notation "{A: A }" := (A%assertion)
  (at level 0, A at level 100, no associativity, only parsing).

(* Constructor notations *)
Notation "# p" := (APredicate p) : assertion_scope.
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

(* Predicate notations *)
Notation AFalse := (APredicate PFalse).
Notation AEqual tl tr := (APredicate (PEqual tl tr)).
Notation "tl = tr" := (AEqual tl tr) : assertion_scope.
Notation AIn t ts := (APredicate (PIn t ts)).
Notation "t \in ts" := (AIn t ts) : assertion_scope.
Notation ACorrect tn := (APredicate (PCorrect tn)).
Notation "'correct' tn" := (ACorrect tn)
  (at level 0, no associativity) : assertion_scope.

(* Derived predicate notations *)
Notation ATrue := (ANot AFalse).
Notation ANotEqual tl tr := (ANot (AEqual tl tr)).
Notation "tl <> tr" := (ANotEqual tl tr) : assertion_scope.
Notation ANotIn t ts := (ANot (AIn t ts)).
Notation "t \notin ts" := (ANotIn t ts) : assertion_scope.

(* Derived propositional operators *)
Notation AAnd Al Ar := (ANot (AOr (ANot Al) (ANot Ar))).
Notation "Al /\ Ar" := (AAnd Al Ar) : assertion_scope.
Notation AIf Al Ar := (AOr (ANot Al) Ar).
Notation "Al -> Ar" := (AIf Al Ar) : assertion_scope.
Notation AIff Al Ar := (AAnd (AIf Al Ar) (AIf Ar Al)).
Notation "Al <-> Ar" := (AIff Al Ar) : assertion_scope.
Notation AExists v A := (ANot (AForAll v (ANot A))).
Notation "exists: v , A" := (AExists v A)
  (at level 65, v at level 99, A at level 200, right associativity)
  : assertion_scope.

(* Derived strict and immediate future temporal operators *)
Notation AEventually' A := (AUntil' ATrue A).
Notation "eventually^ A" := (AEventually' A)
  (at level 60, right associativity) : assertion_scope.
Notation AAlways' A := (ANot (AEventually' (ANot A))).
Notation "always^ A" := (AAlways' A)
  (at level 60, right associativity) : assertion_scope.
Notation AUnless' Al Ar := (AOr (AAlways' Al) (AUntil' Al Ar)).
Notation "Al unless^ Ar" := (AUnless' Al Ar)
  (at level 60, right associativity) : assertion_scope.
Notation ANext A := (AUntil' AFalse A).
Notation "'next' A" := (ANext A)
  (at level 60, right associativity) : assertion_scope.

(* Derived strict and immediate past temporal operators *)
Notation AEventuallyP' A := (ASince' ATrue A).
Notation "eventuallyp^ A" := (AEventuallyP' A)
  (at level 60, right associativity) : assertion_scope.
Notation AAlwaysP' A := (ANot (AEventuallyP' (ANot A))).
Notation "alwaysp^ A" := (AAlwaysP' A)
  (at level 60, right associativity) : assertion_scope.
Notation ABackTo' Al Ar := (AOr (AAlwaysP' Al) (ASince' Al Ar)).
Notation "Al backto^ Ar" := (ABackTo' Al Ar)
  (at level 60, right associativity) : assertion_scope.
Notation APrevious A := (ASince' AFalse A).
Notation "'previous' A" := (APrevious A)
  (at level 60, right associativity) : assertion_scope.
Notation APrevious' A := (ANot (APrevious (ANot A))).
Notation "previous^ A" := (APrevious' A)
  (at level 60, right associativity) : assertion_scope.

(* Derived reflexive future temporal operators *)
Notation AEventually A := (AOr A (AEventually' A)).
Notation "'eventually' A" := (AEventually A)
  (at level 60, right associativity) : assertion_scope.
Notation AAlways A := (AAnd A (AAlways' A)).
Notation "'always' A" := (AAlways A)
  (at level 60, right associativity) : assertion_scope.
Notation AUntil Al Ar := (AOr Ar (AAnd Al (AUntil' Al Ar))).
Notation "Al 'until' Ar" := (AUntil Al Ar)
  (at level 60, right associativity) : assertion_scope.
Notation AUnless Al Ar := (AOr Ar (AAnd Al (AUnless' Al Ar))).
Notation "Al 'unless' Ar" := (AUnless Al Ar)
  (at level 60, right associativity) : assertion_scope.

(* Derived reflexive past temporal operators *)
Notation AEventuallyP A := (AOr A (AEventuallyP' A)).
Notation "'eventuallyp' A" := (AEventuallyP A)
  (at level 60, right associativity) : assertion_scope.
Notation AAlwaysP A := (AAnd A (AAlwaysP' A)).
Notation "'alwaysp' A" := (AAlwaysP A)
  (at level 60, right associativity) : assertion_scope.
Notation ASince Al Ar := (AOr Ar (AAnd Al (ASince' Al Ar))).
Notation "Al 'since' Ar" := (ASince Al Ar)
  (at level 60, right associativity) : assertion_scope.
Notation ABackTo Al Ar := (AOr Ar (AAnd Al (ABackTo' Al Ar))).
Notation "Al 'backto' Ar" := (ABackTo Al Ar)
  (at level 60, right associativity) : assertion_scope.

(* Additional temporal operators *)
Notation AEntails Al Ar := (AAlways (AIf Al Ar)).
Notation "Al =>> Ar" := (AEntails Al Ar)
  (at level 99, right associativity) : assertion_scope.
Notation ACongruent Al Ar := (AAnd (AEntails Al Ar) (AEntails Ar Al)).
Notation "Al <=> Ar" := (ACongruent Al Ar)
  (at level 95, no associativity) : assertion_scope.
Notation AFollowedBy Al Ar := (AEntails Al (AEventually Ar)).
Notation "Al ~> Ar" := (AFollowedBy Al Ar)
  (at level 90, right associativity) : assertion_scope.
Notation APrecededBy Al Ar := (AEntails Al (AEventuallyP Ar)).
Notation "Al <~ Ar" := (APrecededBy Al Ar)
  (at level 90, right associativity) : assertion_scope.

(* Component syntactic sugar *)
Notation AWhenOn tn A := (AAnd (AEqual "Fn" tn) A).
Notation "when-on[ tn ] A" := (AWhenOn tn A)
  (at level 60, right associativity) : assertion_scope.
Notation AWhenTopRequest te :=
  (AAnd (AEqual "Fd" []) (AAnd (AEqual "Fo" CRequest) (AEqual "Fe" te))).
Notation "when[]-> te" := (AWhenTopRequest te)
  (at level 60, no associativity) : assertion_scope.
Notation AWhenTopIndication te :=
  (AAnd (AEqual "Fd" []) (AAnd (AEqual "Fo" CIndication) (AEqual "Fe" te))).
Notation "when[]<- te" := (AWhenTopIndication te)
  (at level 60, no associativity) : assertion_scope.
Notation AWhenTopPeriodic te :=
  (AAnd (AEqual "Fd" []) (AAnd (AEqual "Fo" CPeriodic) (AEqual "Fe" te))).
Notation "when[]~> te" := (AWhenTopPeriodic te)
  (at level 60, no associativity) : assertion_scope.
Notation AWhenSubRequest ti te :=
  (AAnd (AEqual "Fd" [ti]) (AAnd (AEqual "Fo" CRequest) (AEqual "Fe" te))).
Notation "when[ ti ]-> te" := (AWhenSubRequest ti te)
  (at level 60, no associativity) : assertion_scope.
Notation AWhenSubIndication ti te :=
  (AAnd (AEqual "Fd" [ti]) (AAnd (AEqual "Fo" CIndication) (AEqual "Fe" te))).
Notation "when[ ti ]<- te" := (AWhenSubIndication ti te)
  (at level 60, no associativity) : assertion_scope.
Notation AWhenSubPeriodic ti te :=
  (AAnd (AEqual "Fd" [ti]) (AAnd (AEqual "Fo" CPeriodic) (AEqual "Fe" te))).
Notation "when[ ti ]~> te" := (AWhenSubPeriodic ti te)
  (at level 60, no associativity) : assertion_scope.
Notation AWhenSelf :=
  (AOr
    (AExists "i" (AAnd (AEqual "Fd" ["i"]) (AEqual "Fo" CIndication)))
    (AOr
      (AAnd (AEqual "Fd" []) (AEqual "Fo" CRequest))
      (AAnd (AEqual "Fd" []) (AEqual "Fo" CPeriodic)))).
Notation "when-self" := (AWhenSelf)
  (at level 60, no associativity) : assertion_scope.
