(* TLC in Coq
 *
 * Module: tlc.syntax.pattern
 * Purpose: Contains the syntax of patterns.
 *)

Require Import mathcomp.ssreflect.eqtype.
Require Import mathcomp.ssreflect.ssrbool.
Require Import mathcomp.ssreflect.ssreflect.
Require Import mathcomp.ssreflect.ssrnat.
Require Import tlc.syntax.constructor.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Forms of patterns in matching expressions *)
Inductive pattern :=
| PWildcard
| PParameter (j : nat)
| PConstructor (c : constructor)
| PApplication (f a : pattern).

(* Equality *)
Section eq.

  (* Boolean equality *)
  Fixpoint pattern_eq p1 p2 :=
    match p1, p2 with
    | PWildcard, PWildcard => true
    | PParameter j1, PParameter j2 => j1 == j2
    | PConstructor c1, PConstructor c2 => c1 == c2
    | PApplication f1 a1, PApplication f2 a2 =>
      pattern_eq f1 f2 && pattern_eq a1 a2
    | _, _ => false
    end.

  (* Boolean equality reflection *)
  Lemma pattern_eqP : Equality.axiom pattern_eq.
  Proof.
    elim=> [| j1 | c1 | f1 IHf a1 IHa] [| j2 | c2 | f2 a2] //=;
      try by constructor.
    - by have [<- | neqx] := j1 =P j2; last (by right; case); constructor.
    - by have [<- | neqx] := c1 =P c2; last (by right; case); constructor.
    - have [<- | neqx] := IHf f2; last (by right; case); simpl.
      have [<- | neqx] := IHa a2; last (by right; case); simpl.
      by constructor.
  Qed.

  (* EqType canonical structures *)
  Definition pattern_eqMixin := EqMixin pattern_eqP.
  Canonical pattern_eqType := EqType pattern pattern_eqMixin.

End eq.

(* Constructor coercions *)
Coercion PConstructor : constructor >-> pattern.

(* Notation scope *)
Declare Scope pattern_scope.
Bind Scope pattern_scope with pattern.
Delimit Scope pattern_scope with pattern.

Notation "{-p p -}" := (p%pattern)
  (at level 0, p at level 100, no associativity, only parsing).

(* Constructor notations *)
Notation "'%'" := PWildcard
  (at level 0, no associativity) : pattern_scope.
Notation "$ j" := (PParameter j)
  (at level 0, j at level 0, no associativity, format "'$' j") : pattern_scope.
Notation "f ' a" := (PApplication f a)
  (at level 10, left associativity) : pattern_scope.

(* Derived constructor notations for pairs *)
Definition PPair p1 p2 := {-p CPair ' p1 ' p2 -}.
Notation "( p1 , p2 , .. , pn )" := (PPair (.. (PPair p1 p2) ..) pn)
  : pattern_scope.

(* Derived constructor notations for booleans *)
Definition PTrue := PConstructor CTrue.
Definition PFalse := PConstructor CFalse.
Definition pattern_of_bool b := if b then PTrue else PFalse.
Coercion pattern_of_bool : bool >-> pattern.

(* Derived constructor notations for naturals *)
Definition PZero := PConstructor CZero.
Definition PSucc n := {-p CSucc ' n -}.
Notation "n .+1" := (PSucc n) : pattern_scope.
Fixpoint pattern_of_nat n :=
  match n with
  | 0 => PZero
  | n.+1 => PSucc (pattern_of_nat n)
  end.
Fixpoint nat_of_pattern p :=
  match p with
  | PConstructor CZero => Some 0
  | PApplication (PConstructor CSucc) p' =>
    match nat_of_pattern p' with
    | Some n' => Some (n'.+1)
    | None => None
    end
  | _ => None
  end.
Definition pattern_of_uint n :=
  pattern_of_nat (Nat.of_num_uint n).
Definition uint_of_pattern p :=
  match nat_of_pattern p with
  | Some n => Some (Nat.to_num_uint n)
  | None => None
  end.
Numeral Notation pattern pattern_of_uint uint_of_pattern : pattern_scope.

(* Derived constructor notations for lists *)
Definition PNil := PConstructor CNil.
Notation "[ ]" := PNil : pattern_scope.
Definition PCons p ps := {-p CCons ' p ' ps -}.
Notation "p :: ps" := (PCons p ps) : pattern_scope.
Notation "[ p1 , .. , pn ]" := {-p p1 :: (.. (pn :: []) ..) -}
  : pattern_scope.
