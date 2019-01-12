Require Import TLC.Syntax.Constant.
Require Import TLC.Syntax.Flexible.
Require Import TLC.Utility.Fin.
Require Import Coq.Arith.PeanoNat.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Expression terms of the language *)
Inductive expression : Type :=
| EVariable (n : nat)
| EConstant (c : constant)
| EFlexible (f : flexible)
| EApplication (e1 e2 : expression).

(* Decidable equality *)
Lemma expression_eq_dec (e e' : expression) : {e = e'} + {e <> e'}.
Proof.
  decide equality.
  - destruct (Nat.eq_dec n n0); [subst; now left | now right].
  - destruct (constant_eq_dec c c0); [subst; now left | now right].
  - destruct (flexible_eq_dec f f0); [subst; now left | now right].
Defined.

Fixpoint expression_eqb e e' :=
  match e, e' with
  | EVariable n, EVariable n' => Nat.eqb n n'
  | EConstant c, EConstant c' => constant_eqb c c'
  | EFlexible f, EFlexible f' => flexible_eqb f f'
  | EApplication e1 e2, EApplication e1' e2' =>
    andb (expression_eqb e1 e1') (expression_eqb e2 e2')
  | _, _ => false
  end.

Lemma expression_eqb_refl e : expression_eqb e e = true.
Proof.
  induction e; simpl.
  - apply Nat.eqb_refl.
  - apply constant_eqb_refl.
  - apply flexible_eqb_refl.
  - now rewrite IHe1, IHe2.
Qed.

(* Notation scope *)
Delimit Scope tlc_expression_scope with e.
Bind Scope tlc_expression_scope with expression.

(* Constructor notations *)
Notation "$ x" := (EVariable x%fin) (at level 0) : tlc_expression_scope.
Notation "^ x" := (EConstant x) (at level 0) : tlc_expression_scope.
Notation "` x" := (EFlexible x) (at level 0) : tlc_expression_scope.
Notation "x <- y" := (EApplication x y)
  (at level 5, right associativity, y at level 99) : tlc_expression_scope.

(* Product constructor notations *)
Notation "( x , y , .. , z )" := (^CPair <- .. (^CPair <- x <- y) .. <- z)%e
  : tlc_expression_scope.

(* List constructor notations *)
Notation "[ ]" := (^CNil)%e : tlc_expression_scope.
Notation "x :: y" := (^CCons <- x <- y)%e : tlc_expression_scope.
Notation "[ x ]" := (x :: [])%e : tlc_expression_scope.
Notation "[ x ; y ; .. ; z ]" :=
  (^CCons <- x <- (^CCons <- y <- .. (^CCons <- z <- ^CNil) ..))%e
  : tlc_expression_scope.

(* Natural constructor notations *)
Fixpoint ENatural n : expression :=
  match n with
  | O => ^CZero
  | S n' => ^CSucc <- ENatural n'
  end.
Notation "# x" := (ENatural x%nat) (at level 0) : tlc_expression_scope.

(* Coercions *)
Coercion EConstant : constant >-> expression.
Coercion EFlexible : flexible >-> expression.
Coercion ENatural : nat >-> expression.
