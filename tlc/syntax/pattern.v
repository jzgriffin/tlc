(* TLC in Coq
 *
 * Module: tlc.syntax.pattern
 * Purpose: Contains the syntax of patterns.
 *)

Require Import mathcomp.ssreflect.eqtype.
Require Import mathcomp.ssreflect.ssrbool.
Require Import mathcomp.ssreflect.ssreflect.
Require Import mathcomp.ssreflect.ssrnat.
Require Import tlc.operation.orientation.
Require Import tlc.operation.periodic_event.
Require Import tlc.syntax.constructor.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Forms of patterns in let and match expressions
 * Every literal constructor must have one or more corresponding constructors
 * in this type.  It is not necessary to modify this type for new data
 * constructors.
 *)
Inductive pattern :=
| PWildcard (* Non-binding placeholder *)
| PBinding (* Binding placeholder *)
| PConstructor (c : constructor)
| PApplication (pf pa : pattern)
(* Literals *)
| PLUnit (u : unit)
| PLBoolean (b : bool)
| PLNatural (n : nat)
| PLSucc (p : pattern)
| PLOrientation (o : orientation)
| PLPeriodic (p : periodic_event).

(* Equality *)
Section eq.

  (* Boolean equality *)
  Fixpoint pattern_eq pl pr :=
    match pl, pr with
    | PWildcard, PWildcard => true
    | PWildcard, _ => false
    | PBinding, PBinding => true
    | PBinding, _ => false
    | PConstructor cl, PConstructor cr => cl == cr
    | PConstructor _, _ => false
    | PApplication pfl pal, PApplication pfr par =>
      pattern_eq pfl pfr && pattern_eq pal par
    | PApplication _ _, _ => false
    | PLUnit ul, PLUnit ur => ul == ur
    | PLUnit _, _ => false
    | PLBoolean bl, PLBoolean br => bl == br
    | PLBoolean _, _ => false
    | PLNatural nl, PLNatural nr => nl == nr
    | PLNatural _, _ => false
    | PLSucc pl, PLSucc pr => pattern_eq pl pr
    | PLSucc _, _ => false
    | PLOrientation ol, PLOrientation or => ol == or
    | PLOrientation _, _ => false
    | PLPeriodic pl, PLPeriodic pr => pl == pr
    | PLPeriodic _, _ => false
    end.

  (* Boolean equality reflection *)
  Lemma pattern_eqP : Equality.axiom pattern_eq.
  Proof.
    elim=> [| | cl | pfl IHpf pal IHpa | ul | bl | nl | pl IHp | ol | pl]
      [| | cr | pfr par | ur | br | nr | pr | or | pr] //=;
      try by constructor.
    - case H: (cl == cr); move/eqP: H => H //=; subst;
        last by constructor; move=> [].
      by constructor.
    - case H: (pattern_eq pfl pfr); move/IHpf: H => H //=; subst;
        last by constructor; move=> [].
      case H: (pattern_eq pal par); move/IHpa: H => H //=; subst;
        last by constructor; move=> [].
      by constructor.
    - case H: (ul == ur); move/eqP: H => H //=; subst;
        last by constructor; move=> [].
      by constructor.
    - case H: (bl == br); move/eqP: H => H //=; subst;
        last by constructor; move=> [].
      by constructor.
    - case H: (nl == nr); move/eqP: H => H //=; subst;
        last by constructor; move=> [].
      by constructor.
    - case H: (pattern_eq pl pr); move/IHp: H => H //=; subst;
        last by constructor; move=> [].
      by constructor.
    - case H: (ol == or); move/eqP: H => H //=; subst;
        last by constructor; move=> [].
      by constructor.
    - case H: (pl == pr); move/eqP: H => H //=; subst;
        last by constructor; move=> [].
      by constructor.
  Qed.

  (* EqType canonical structures *)
  Canonical Structure pattern_eqMixin :=
    Eval hnf in EqMixin pattern_eqP.
  Canonical Structure pattern_eqType :=
    Eval hnf in EqType pattern pattern_eqMixin.

End eq.

(* Constructor coercions *)
Coercion PConstructor : constructor >-> pattern.
Coercion PLUnit : unit >-> pattern.
Coercion PLBoolean : bool >-> pattern.
Coercion PLNatural : nat >-> pattern.
Coercion PLOrientation : orientation >-> pattern.
Coercion PLPeriodic : periodic_event >-> pattern.

(* Notation scope *)
Bind Scope pattern_scope with pattern.
Delimit Scope pattern_scope with pattern.
Notation "{p: p }" := (p%pattern)
  (at level 0, p at level 100, no associativity, only parsing).

(* Constructor notations *)
Notation "'%'" := (PWildcard)
  (at level 0, no associativity) : pattern_scope.
Notation "'#'" := (PBinding)
  (at level 0, no associativity) : pattern_scope.
Notation "pf $ pa" := (PApplication pf pa)
  (at level 10, left associativity) : pattern_scope.
Notation "p .+1" := (PLSucc p) : pattern_scope.

(* Pair constructor notations *)
Definition PPair pl pr := {p: CPair $ pl $ pr}.
Notation "( p1 , p2 , .. , pn )" :=
  {p: PPair (.. (PPair p1 p2) ..) pn} : pattern_scope.

(* List constructor notations *)
Definition PNil := PConstructor CNil.
Notation "[ ]" := PNil : pattern_scope.
Definition PCons p ps := {p: CCons $ p $ ps}.
Notation "p :: ps" := (PCons p ps) : pattern_scope.
Notation "[ p1 , .. , pn ]" := {p: p1 :: (.. (pn :: []) ..)}
  : pattern_scope.
