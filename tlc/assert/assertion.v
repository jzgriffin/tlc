Require Import mathcomp.ssreflect.eqtype.
Require Import mathcomp.ssreflect.ssrbool.
Require Import mathcomp.ssreflect.ssreflect.
Require Import tlc.assert.predicate.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Assertion type *)
Inductive assertion : Type :=
| AFalse : assertion
| ANot : assertion -> assertion
| AOr : assertion -> assertion -> assertion
| APredicate : predicate -> assertion.

(* Constructor coercions *)
Coercion APredicate : predicate >-> assertion.

(* Notation scope *)
Delimit Scope assertion_scope with A.
Bind Scope assertion_scope with assertion.
Notation "{A: A }" := (A%A) (at level 0, A at level 99, no associativity,
  only parsing).

(* Constructor notations *)
Notation "~ A" := (ANot A) : assertion_scope.
Notation "Al \/ Ar" := (AOr Al Ar) : assertion_scope.

(* Derived predicate operators *)
Notation "el = er" := (APredicate (PEqual el er)) : assertion_scope.
Notation "e '\in' es" := (APredicate (PMember e es)) : assertion_scope.

(* Derived propositional operators *)
Definition ATrue := {A: ~AFalse}.
Definition AAnd Al Ar := {A: ~(~Al \/ ~Ar)}.
Notation "Al /\ Ar" := (AAnd Al Ar) : assertion_scope.
Definition AIf Al Ar := {A: ~Al \/ Ar}.
Notation "Al -> Ar" := (AIf Al Ar) : assertion_scope.
Definition AIff Al Ar := {A: (Al -> Ar) /\ (Ar -> Al)}.
Notation "Al <-> Ar" := (AIff Al Ar) : assertion_scope.

(* Equality *)
Section eq.

  (* Boolean equality *)
  Fixpoint assertion_eq Al Ar :=
    match Al, Ar with
    | AFalse, AFalse => true
    | AFalse, _ => false
    | ANot Al', ANot Ar' => assertion_eq Al' Ar'
    | ANot _, _ => false
    | AOr All Arl, AOr Alr Arr => assertion_eq All Alr && assertion_eq Arl Arr
    | AOr _ _, _ => false
    | APredicate pl, APredicate pr => pl == pr
    | APredicate _, _ => false
    end.

  (* Boolean equality reflection *)
  Lemma assertion_eqP : Equality.axiom assertion_eq.
  Proof.
    elim=> [| Al IHAl | All IHAll Arl IHArl | pl] [| Ar | Alr Arr | pr] //=;
      try by constructor.
    - case H: (assertion_eq Al Ar); move/IHAl: H => H //=; subst;
        last by constructor; move=> [].
      by constructor.
    - case H: (assertion_eq All Alr); move/IHAll: H => H //=; subst;
        last by constructor; move=> [].
      case H: (assertion_eq Arl Arr); move/IHArl: H => H //=; subst;
        last by constructor; move=> [].
      by constructor.
    - case H: (pl == pr); move/eqP: H => H //=; subst;
        last by constructor; move=> [].
      by constructor.
  Qed.

  (* EqType canonical structures *)
  Canonical Structure assertion_eqMixin := EqMixin assertion_eqP.
  Canonical Structure assertion_eqType :=
    Eval hnf in EqType assertion assertion_eqMixin.

End eq.
