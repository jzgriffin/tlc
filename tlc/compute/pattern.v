Require Import mathcomp.ssreflect.eqtype.
Require Import mathcomp.ssreflect.seq.
Require Import mathcomp.ssreflect.ssrbool.
Require Import mathcomp.ssreflect.ssreflect.
Require Import tlc.compute.constructor.
Require Import tlc.compute.variable.
Require Import tlc.utility.set.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Pattern type *)
Inductive pattern : Type :=
| PConstructor : constructor -> pattern
| PVariable : variable -> pattern
| PApplication : pattern -> pattern -> pattern.

(* Constructor coercions *)
Coercion PConstructor : constructor >-> pattern.
Coercion PVariable : variable >-> pattern.

(* Notation scope *)
Delimit Scope pattern_scope with p.
Bind Scope pattern_scope with pattern.
Notation "{p: p }" := (p%p) (at level 0, p at level 99, no associativity,
  only parsing).

(* Pattern constructor notations *)
Notation "% c" := (PConstructor c)
  (at level 0, c at level 0, no associativity, only parsing, format "'%' c")
  : pattern_scope.
Notation "$ v" := (PVariable v)
  (at level 0, v at level 0, no associativity, only parsing, format "'$' v")
  : pattern_scope.
Notation "pl $ pr" := (PApplication pl pr)
  (at level 10, left associativity) : pattern_scope.

(* Constructor pattern notations *)
Notation "( p1 , p2 , .. , pn )" :=
  {p: CPair $ (.. (CPair $ p1 $ p2) ..) $ pn} : pattern_scope.
Notation "[ ]" := {p: %CNil} : pattern_scope.
Notation "p :: ps" := {p: CCons $ p $ ps} : pattern_scope.
Notation "[ p ]" := {p: p :: []} : pattern_scope.
Notation "[ p1 , .. , pn ]" := {p: p1 :: (.. (CCons $ pn $ []) ..)}
  : pattern_scope.

(* Equality *)
Section eq.

  (* Boolean equality *)
  Fixpoint pattern_eq pl pr :=
    match pl, pr with
    | PConstructor cl, PConstructor cr => cl == cr
    | PConstructor _, _ => false
    | PVariable vl, PVariable vr => vl == vr
    | PVariable _, _ => false
    | PApplication pll prl, PApplication plr prr =>
      pattern_eq pll plr && pattern_eq prl prr
    | PApplication _ _, _ => false
    end.

  (* Boolean equality reflection *)
  Lemma pattern_eqP : Equality.axiom pattern_eq.
  Proof.
    elim=> [cl | vl | pll IHpl prl IHpr] [cr | vr | plr prr] //=;
      try by constructor.
    - case H: (cl == cr); move/eqP: H => H; constructor; first by rewrite H.
      by move=> [].
    - case H: (vl == vr); move/eqP: H => H; constructor; first by rewrite H.
      by move=> [].
    - case Hpl: (pattern_eq pll plr); move/IHpl: Hpl => Hpl //=; subst;
        last by constructor; move=> [].
      case Hpr: (pattern_eq prl prr); move/IHpr: Hpr => Hpr //=; subst;
        last by constructor; move=> [].
      by constructor.
  Qed.

  (* EqType canonical structures *)
  Canonical Structure pattern_eqMixin := EqMixin pattern_eqP.
  Canonical Structure pattern_eqType :=
    Eval hnf in EqType pattern pattern_eqMixin.

End eq.

(* Variables bound in pattern *)
Fixpoint pv p : set [eqType of variable] :=
  match p with
  | PConstructor _ => [::]
  | PVariable v => [:: v]
  | PApplication pl pr => pv pl {+} pv pr
  end.
