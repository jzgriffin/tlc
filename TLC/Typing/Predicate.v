Require Import TLC.Syntax.Predicate.
Require Import TLC.Typing.Component.
Require Import TLC.Typing.Context.
Require Import TLC.Typing.Expression.
Require Import TLC.Typing.Type.

Section typed_predicate.

  Reserved Notation "x |- y" (at level 0, no associativity).

  (* Type-checked predicate terms *)
  Inductive typed_predicate {P} {C : component P} :
    forall G : context, predicate -> Type :=
  | TPEqual {G t} e1 e2 :
    G |-e e1 : t | C ->
    G |-e e2 : t | C ->
    G |- (PEqual e1 e2)
  | TPMember {G t} e1 e2 :
    G |-e e1 : t | C ->
    G |-e e2 : (TList t) | C ->
    G |- (PMember e1 e2)
  | TPCorrect {G} e1 :
    G |-e e1 : TNode | C ->
    G |- (PCorrect e1)
  where "x |- y" := (typed_predicate x y) : type_scope.

End typed_predicate.

Arguments typed_predicate : clear implicits.
Arguments typed_predicate {P} C.

(* Notations for typed-checked predicates *)
Notation "x |-p y | z" := (typed_predicate z x y)
  (at level 0, no associativity) : type_scope.
