Require Import TLC.Syntax.Constant.
Require Import TLC.Syntax.Expression.
Require Import TLC.Syntax.Flexible.
Require Import TLC.Syntax.Predicate.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Formula terms of the language *)
Inductive formula : Type :=
(* Propositional logic *)
| FFalse
| FNot (f1 : formula)
| FOr (f1 f2 : formula)
(* First-order logic *)
| FPredicate (p : predicate)
| FForAll (f1 : formula)
(* Temporal logic *)
| FUntil' (f1 f2 : formula)
| FSince' (f1 f2 : formula).

(* Decidable equality *)
Lemma formula_eq_dec (f f' : formula) : {f = f'} + {f <> f'}.
Proof.
  decide equality.
  - destruct (predicate_eq_dec p p0); [subst; now left | now right].
Defined.

Fixpoint formula_eqb f f' :=
  match f, f' with
  (* Propositional logic *)
  | FFalse, FFalse => true
  | FNot f1, FNot f1' => formula_eqb f1 f1'
  | FOr f1 f2, FOr f1' f2' =>
    andb (formula_eqb f1 f1') (formula_eqb f2 f2')
  (* First-order logic *)
  | FPredicate p, FPredicate p' => predicate_eqb p p'
  | FForAll f1, FForAll f1' => formula_eqb f1 f1'
  (* Temporal logic *)
  | FUntil' f1 f2, FUntil' f1' f2' =>
    andb (formula_eqb f1 f1') (formula_eqb f2 f2')
  | FSince' f1 f2, FSince' f1' f2' =>
    andb (formula_eqb f1 f1') (formula_eqb f2 f2')
  | _, _ => false
  end.

Lemma formula_eqb_refl f : formula_eqb f f = true.
Proof.
  induction f; simpl; try reflexivity;
    (try now rewrite IHf);
    (try now rewrite IHf1, IHf2).
  - apply predicate_eqb_refl.
Qed.

(* Constructor coercions *)
Coercion FPredicate : predicate >-> formula.

(* Notation scope *)
Delimit Scope tlc_formula_scope with f.
Bind Scope tlc_formula_scope with formula.

(* Constructor notations *)
Notation "~ x" := (FNot x) : tlc_formula_scope.
Notation "x \/ y" := (FOr x y) : tlc_formula_scope.
Notation "'forall:' x" := (FForAll x)
  (at level 65, right associativity) : tlc_formula_scope.
Notation "x 'until^' y" := (FUntil' x y)
  (at level 60, right associativity) : tlc_formula_scope.
Notation "x 'since^' y" := (FSince' x y)
  (at level 60, right associativity) : tlc_formula_scope.

(* Derived propositional operators *)
Definition FTrue : formula := ~FFalse.
Definition FAnd (f1 f2 : formula) : formula := ~(~f1 \/ ~f2).
Notation "x /\ y" := (FAnd x y) : tlc_formula_scope.
Definition FIf (f1 f2 : formula) : formula := ~f1 \/ f2.
Notation "x -> y" := (FIf x y) : tlc_formula_scope.
Definition FIff (f1 f2 : formula) : formula := (f1 -> f2) /\ (f2 -> f1).
Notation "x <-> y" := (FIff x y) : tlc_formula_scope.

(* Derived first-order operators *)
Definition FExists (f1 : formula) : formula := ~forall: ~f1.
Notation "'exists:' x" := (FExists x)
  (at level 65, right associativity) : tlc_formula_scope.

(* Derived strict and immediate future temporal operators *)
Definition FEventually' (f : formula) : formula := FTrue until^ f.
Notation "'eventually^' x" := (FEventually' x)
  (at level 60, right associativity) : tlc_formula_scope.
Definition FAlways' (f : formula) : formula := ~eventually^ ~f.
Notation "'always^' x" := (FAlways' x)
  (at level 60, right associativity) : tlc_formula_scope.
Definition FUnless' (f1 f2 : formula) : formula :=
  always^ f1 \/ (f1 until^ f2).
Notation "x 'unless^' y" := (FUnless' x y)
  (at level 60, right associativity) : tlc_formula_scope.
Definition FNext (f : formula) : formula := FFalse until^ f.
Notation "'next' x" := (FNext x)
  (at level 60, right associativity) : tlc_formula_scope.

(* Derived strict and immediate past temporal operators *)
Definition FEventuallyP' (f : formula) : formula := FTrue since^ f.
Notation "'eventuallyp^' x" := (FEventuallyP' x)
  (at level 60, right associativity) : tlc_formula_scope.
Definition FAlwaysP' (f : formula) : formula := ~eventuallyp^ ~f.
Notation "'alwaysp^' x" := (FAlwaysP' x)
  (at level 60, right associativity) : tlc_formula_scope.
Definition FBackTo' (f1 f2 : formula) : formula :=
  alwaysp^ f1 \/ (f1 since^ f2).
Notation "x 'backto^' y" := (FBackTo' x y)
  (at level 60, right associativity) : tlc_formula_scope.
Definition FPrevious (f : formula) : formula := FFalse since^ f.
Notation "'previous' x" := (FPrevious x)
  (at level 60, right associativity) : tlc_formula_scope.
Definition FPrevious' (f : formula) : formula := ~previous ~f.
Notation "'previous^' x" := (FPrevious' x)
  (at level 60, right associativity) : tlc_formula_scope.

(* Derived reflexive future temporal operators *)
Definition FEventually (f : formula) : formula := f \/ eventually^ f.
Notation "'eventually' x" := (FEventually x)
  (at level 60, right associativity) : tlc_formula_scope.
Definition FAlways (f : formula) : formula := f /\ always^ f.
Notation "'always' x" := (FAlways x)
  (at level 60, right associativity) : tlc_formula_scope.
Definition FUntil (f1 f2 : formula) : formula :=
  f2 \/ (f1 /\ (f1 until^ f2)).
Notation "x 'until' y" := (FUntil x y)
  (at level 60, right associativity) : tlc_formula_scope.
Definition FUnless (f1 f2 : formula) : formula :=
  f2 \/ (f1 /\ (f1 unless^ f2)).
Notation "x 'unless' y" := (FUnless x y)
  (at level 60, right associativity) : tlc_formula_scope.

(* Derived reflexive past temporal operators *)
Definition FEventuallyP (f : formula) : formula := f \/ eventuallyp^ f.
Notation "'eventuallyp' x" := (FEventuallyP x)
  (at level 60, right associativity) : tlc_formula_scope.
Definition FAlwaysP (f : formula) : formula := f /\ alwaysp^ f.
Notation "'alwaysp' x" := (FAlwaysP x)
  (at level 60, right associativity) : tlc_formula_scope.
Definition FSince (f1 f2 : formula) : formula :=
  f2 \/ (f1 /\ (f1 since^ f2)).
Notation "x 'since' y" := (FSince x y)
  (at level 60, right associativity) : tlc_formula_scope.
Definition FBackTo (f1 f2 : formula) : formula :=
  f2 \/ (f1 /\ (f1 backto^ f2)).
Notation "x 'backto' y" := (FBackTo x y)
  (at level 60, right associativity) : tlc_formula_scope.

(* Additional temporal operators *)
Definition FEntails (f1 f2 : formula) : formula := always (f1 -> f2).
Notation "x =>> y" := (FEntails x y)
  (at level 99, right associativity) : tlc_formula_scope.
Definition FCongruent (f1 f2 : formula) : formula :=
  (f1 =>> f2) /\ (f2 =>> f1).
Notation "x <=> y" := (FCongruent x y)
  (at level 95, no associativity) : tlc_formula_scope.
Definition FLeadsTo (f1 f2 : formula) : formula := f1 =>> eventually f2.
Notation "x ~> y" := (FLeadsTo x y)
  (at level 90, right associativity) : tlc_formula_scope.
Definition FPrecededBy (f1 f2 : formula) : formula :=
  f1 =>> eventuallyp f2.
Notation "x <~ y" := (FPrecededBy x y)
  (at level 90, right associativity) : tlc_formula_scope.

(* Predicate constructor notations *)
Notation "x = y" := (PEqual x y) : tlc_formula_scope.
Notation "x '\in' y" := (PMember x y)
  (at level 20, no associativity) : tlc_formula_scope.

(* Label operators *)
Definition FWhenOn (n : expression) (f : formula) : formula :=
  `Fn = n /\ f.
Notation "'when-on[' x ']' y" := (FWhenOn x y)
  (at level 60, right associativity) : tlc_formula_scope.
Definition FWhenTopRequest (e : expression) : formula :=
  `Fd = [] /\ `Fo = ^CORequest /\ `Fe = e.
Notation "'when[]->' x" := (FWhenTopRequest x)
  (at level 60, no associativity) : tlc_formula_scope.
Definition FWhenTopIndication (e : expression) : formula :=
  `Fd = [] /\ `Fo = ^COIndication /\ `Fe = e.
Notation "'when[]<-' x" := (FWhenTopIndication x)
  (at level 60, no associativity) : tlc_formula_scope.
Definition FWhenTopPeriodic (e : expression) : formula :=
  `Fd = [] /\ `Fo = ^COPeriodic /\ `Fe = e.
Notation "'when[]~>' x" := (FWhenTopPeriodic x)
  (at level 60, no associativity) : tlc_formula_scope.
Definition FWhenSubRequest (i e : expression) : formula :=
  `Fd = [i] /\ `Fo = ^CORequest /\ `Fe = e.
Notation "'when[' x ']->' y" := (FWhenSubRequest x y)
  (at level 60, no associativity) : tlc_formula_scope.
Definition FWhenSubIndication (i e : expression) : formula :=
  `Fd = [i] /\ `Fo = ^COIndication /\ `Fe = e.
Notation "'when[' x ']<-' y" := (FWhenSubIndication x y)
  (at level 60, no associativity) : tlc_formula_scope.
Definition FWhenSubPeriodic (i e : expression) : formula :=
  `Fd = [i] /\ `Fo = ^COPeriodic /\ `Fe = e.
Notation "'when[' x ']~>' y" := (FWhenSubPeriodic x y)
  (at level 60, no associativity) : tlc_formula_scope.
Definition FWhenSelf : formula :=
  (`Fd = [] /\ `Fo = ^CORequest) \/
  (`Fd = [] /\ `Fo = ^COPeriodic) \/
  (exists: (`Fd = [$0] /\ `Fo = ^COIndication)).
Notation "'when-self'" := (FWhenSelf)
  (at level 60, no associativity) : tlc_formula_scope.
