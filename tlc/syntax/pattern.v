Require Import mathcomp.ssreflect.eqtype.
Require Import mathcomp.ssreflect.ssrbool.
Require Import mathcomp.ssreflect.ssreflect.
Require Import mathcomp.ssreflect.ssrnat.
Require Import tlc.syntax.constructor.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Forms of patterns in let and match expressions *)
Inductive pattern :=
| PWildcard (* Non-binding placeholder *)
| PBinding (* Binding placeholder *)
| PConstructor (c : constructor)
| PApplication (pf pa : pattern).

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
    end.

  (* Boolean equality reflection *)
  Lemma pattern_eqP : Equality.axiom pattern_eq.
  Proof.
    elim=> [| | cl | pfl IHpf pal IHpa] [| | cr | pfr par] //=;
      try by constructor.
    - case H: (cl == cr); move/eqP: H => H //=; subst;
        last by constructor; move=> [].
      by constructor.
    - case H: (pattern_eq pfl pfr); move/IHpf: H => H //=; subst;
        last by constructor; move=> [].
      case H: (pattern_eq pal par); move/IHpa: H => H //=; subst;
        last by constructor; move=> [].
      by constructor.
  Qed.

  (* EqType canonical structures *)
  Canonical Structure pattern_eqMixin := EqMixin pattern_eqP.
  Canonical Structure pattern_eqType :=
    Eval hnf in EqType pattern pattern_eqMixin.

End eq.

(* Constructor coercions *)
Coercion PConstructor : constructor >-> pattern.

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

(* Pair constructor notations *)
Notation "( p1 , p2 , .. , pn )" :=
  {p: CPair $ (.. (CPair $ p1 $ p2) ..) $ pn} : pattern_scope.

(* Natural constructor notations *)
Notation "0" := (PConstructor CZero) : pattern_scope.
Notation "p .+1" := {p: CSucc $ p} : pattern_scope.

(* List constructor notations *)
Notation "[ ]" := (PConstructor CNil) : pattern_scope.
Notation "p :: ps" := {p: CCons $ p $ ps} : pattern_scope.
Notation "[ p ]" := {p: p :: []} : pattern_scope.
Notation "[ p1 , .. , pn ]" := {p: p1 :: (.. (CCons $ pn $ []) ..)}
  : pattern_scope.

(* Unit coercion *)
Definition PUnit u : pattern :=
  match u with
  | tt => CUnit
  end.

Coercion PUnit : unit >-> pattern.

(* Boolean coercion *)
Definition PBoolean b : pattern :=
  match b with
  | true => CTrue
  | false => CFalse
  end.

Coercion PBoolean : bool >-> pattern.

(* Natural coercion *)
Fixpoint PNatural n : pattern :=
  match n with
  | 0 => CZero
  | n.+1 => (PNatural n).+1
  end.

Coercion PNatural : nat >-> pattern.
