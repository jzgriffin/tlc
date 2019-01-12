Require Import TLC.Syntax.Formula.
Require Import TLC.Typing.Component.
Require Import TLC.Typing.Context.
Require Import TLC.Typing.Expression.
Require Import TLC.Typing.Predicate.
Require Import TLC.Typing.Type.
Require Import Coq.Lists.List.

Section typed_formula.

  Reserved Notation "x |- y" (at level 0, no associativity).

  (* Type-checked formula terms *)
  Inductive typed_formula {P} {C : component P} :
    forall G : context, formula -> Type :=
  (* Propositional logic *)
  | TFFalse {G} :
    G |- FFalse
  | TFNot {G} f1 :
    G |- f1 ->
    G |- ~f1
  | TFOr {G} f1 f2 :
    G |- f1 ->
    G |- f2 ->
    G |- (f1 \/ f2)
  (* First-order logic *)
  | TFPredicate {G} p :
    G |-p p | C ->
    G |- p
  | TFForAll {G t} f1 :
    (t :: G) |- f1 ->
    G |- forall: f1
  where "x |- y" := (typed_formula x y) : type_scope.

End typed_formula.

Arguments typed_formula : clear implicits.
Arguments typed_formula {P} C.

(* Notations for typed-checked formulae *)
Notation "x |-f y | z" := (typed_formula z x y)
  (at level 0, no associativity) : type_scope.
