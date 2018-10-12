From mathcomp.ssreflect
Require Import ssreflect eqtype ssrbool seq.
From tlc.utility
Require Import hseq.
From tlc.assert
Require Import scope type flexible_var rigid_var.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Typed terms representing variables, constants, and applications *)
Inductive term {C} : type -> Type :=
| Flexible (x : flexible_var) : term (type_flexible_var x)
| Rigid {t} (x : @rigid_var C t) : term t
| Const {t} (c : @denote_type C t) : term t
| App {d r} (f : term (d -> r)) (x : term d) : term r.

Coercion Rigid : rigid_var >-> term.

Bind Scope tlc_core_scope with term.

(* Notations for constructing terms *)
Notation "f <- x" :=
  (App f x)
  (at level 10, left associativity) : tlc_core_scope.

(* Extracts the types of rigid variable used in a term *)
Fixpoint term_var_types {C te} (e : @term C te) :=
  match e with
  | Flexible _ => [::]
  | Rigid t _ => [:: t]
  | Const _ _ => [::]
  | App _ _ f x => undup (term_var_types f ++ term_var_types x)
  end.

(* Extracts the rigid variables used in a term *)
Fixpoint term_vars {C te} (e : @term C te) (t : type) : seq (@rigid_var C t) :=
  match e with
  | Flexible _ => [::]
  | Rigid t' x =>
    if t' == t then
      let: n := unwrap_rigid_var x in
      [:: RigidVar t n]
    else [::]
  | Const _ _ => [::]
  | App _ _ f x => undup (term_vars f t ++ term_vars x t)
  end.

(* Transformations *)
Definition substitution {C t} := @rigid_var C t -> option (@term C t).

(* Substitution of terms in place of rigid variables *)
Fixpoint term_subst {C te} (s : forall t, @substitution C t) (e : @term C te)
: @term C te.
  inversion e.
  - (* Flexible *)
    rewrite H; by assumption.
  - (* Rigid *)
    specialize (s _ x); case s => [e' | ]; by assumption.
  - (* Const *)
    by assumption.
  - (* App *)
    specialize (term_subst _ _ s f) as f'.
    specialize (term_subst _ _ s x) as x'.
    by exact: (App f' x').
Defined.
