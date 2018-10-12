From mathcomp.ssreflect
Require Import ssreflect eqtype ssrbool seq.
From tlc.utility
Require Import seq.
From tlc.comp
Require Import component.
From tlc.assert
Require Import scope type rigid_var term atom.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Inductive prop {C} : Type :=
| Atom (a : @atom C)
| Conj (A1 A2 : prop)
| Neg (A : prop)
| Always {t} (x : @rigid_var C t) (A : prop)
| AlwaysF' (A : prop)
| AlwaysP' (A : prop)
| ExistsF' (A : prop)
| ExistsP' (A : prop)
| Next (A : prop)
| Self (A : prop).

Bind Scope tlc_core_scope with prop.

Coercion Atom : atom >-> prop.

(* Basic notation for building propositions *)
Notation "A1 /\ A2" :=
  (Conj A1 A2)
  (at level 80, right associativity) : tlc_core_scope.
Notation "~ A" :=
  (Neg A)
  (at level 75, right associativity) : tlc_core_scope.
Notation "'always:' x , A" :=
  (@Always _ _ x A)
  (at level 65, right associativity) : tlc_core_scope.
Notation "'alwaysf^:' A" :=
  (AlwaysF' A)
  (at level 65, right associativity) : tlc_core_scope.
Notation "'alwaysp^:' A" :=
  (AlwaysP' A)
  (at level 65, right associativity) : tlc_core_scope.
Notation "'existsf^:' A" :=
  (ExistsF' A)
  (at level 65, right associativity) : tlc_core_scope.
Notation "'existsp^:' A" :=
  (ExistsP' A)
  (at level 65, right associativity) : tlc_core_scope.
Notation "'next:' A" :=
  (Next A)
  (at level 65, right associativity) : tlc_core_scope.
Notation "'self:' A" :=
  (Self A)
  (at level 65, right associativity) : tlc_core_scope.

(* Syntactic sugar *)
Definition Disj {C} (A1 A2 : @prop C) : @prop C :=
  ~(~A1 /\ ~A2).
Notation "A1 \/ A2" :=
  (Disj A1 A2)
  (at level 85, right associativity) : tlc_core_scope.

Definition Impl {C} (A1 A2 : @prop C) : @prop C :=
  ~A1 \/ A2.
Notation "A1 -> A2" :=
  (Impl A1 A2)
  (at level 99, right associativity, A2 at level 200) : tlc_core_scope.

Definition Bicond {C} (A1 A2 : @prop C) : @prop C :=
  A1 -> A2 \/ A2 -> A1.
Notation "A1 <-> A2" :=
  (Bicond A1 A2)
  (at level 95, no associativity) : tlc_core_scope.

Definition Exists {C t} (x : rigid_var t) (A : @prop C) : @prop C :=
  ~always: x, ~A.
Notation "'exists:' x , A" :=
  (@Exists _ _ x A)
  (at level 65, right associativity) : tlc_core_scope.

Definition AlwaysF {C} (A : @prop C) : @prop C :=
  A \/ alwaysf^: A.
Notation "'alwaysf:' A" :=
  (AlwaysF A)
  (at level 65, right associativity) : tlc_core_scope.

Definition AlwaysP {C} (A : @prop C) : @prop C :=
  A \/ alwaysp^: A.
Notation "'alwaysp:' A" :=
  (AlwaysP A)
  (at level 65, right associativity) : tlc_core_scope.

Definition ExistsF {C} (A : @prop C) : @prop C :=
  A \/ existsf^: A.
Notation "'existsf:' A" :=
  (ExistsF A)
  (at level 65, right associativity) : tlc_core_scope.

Definition ExistsP {C} (A : @prop C) : @prop C :=
  A \/ existsp^: A.
Notation "'existsp:' A" :=
  (ExistsP A)
  (at level 65, right associativity) : tlc_core_scope.

Definition StrongImpl {C} (A1 A2 : @prop C) : @prop C :=
  (alwaysf: A1) -> A2.
Notation "A1 =>: A2" :=
  (StrongImpl A1 A2)
  (at level 98, right associativity) : tlc_core_scope.
  
Definition StrongBicond {C} (A1 A2 : @prop C) : @prop C :=
  ((alwaysf: A1) -> A2) /\
  ((alwaysf: A2) -> A1).
Notation "A1 <=>: A2" :=
  (StrongBicond A1 A2)
  (at level 98, right associativity) : tlc_core_scope.

Definition LeadsTo {C} (A1 A2 : @prop C) : @prop C :=
  (alwaysf: A1) -> (existsf: A2).
Notation "A1 ~> A2" :=
  (LeadsTo A1 A2)
  (at level 97, right associativity) : tlc_core_scope.

Definition PrecBy {C} (A1 A2 : @prop C) : @prop C :=
  (alwaysf: A1) -> (existsp: A2).
Notation "A1 <~ A2" :=
  (PrecBy A1 A2)
  (at level 97, right associativity) : tlc_core_scope.

(* Extracts the types of rigid variable used in a prop *)
Fixpoint prop_var_types {C} (A : @prop C) :=
  match A with
  | Atom a => term_var_types a
  | Conj A1 A2 => union (prop_var_types A1) (prop_var_types A2)
  | Neg A0 => prop_var_types A0
  | Always _ _ A0 => prop_var_types A0
  | AlwaysF' A0 => prop_var_types A0
  | AlwaysP' A0 => prop_var_types A0
  | ExistsF' A0 => prop_var_types A0
  | ExistsP' A0 => prop_var_types A0
  | Next A0 => prop_var_types A0
  | Self A0 => prop_var_types A0
  end.

(* Extracts the free rigid variables used in a prop *)
Fixpoint prop_free_vars {C} (A : @prop C) (t : type) : seq (@rigid_var C t).
  inversion A.
  - (* Atom *)
    apply (@term_vars _ _ a t).
  - (* Conj *)
    specialize (prop_free_vars _ A1 t) as s1.
    specialize (prop_free_vars _ A2 t) as s2.
    apply (union s1 s2).
  - (* Neg *)
    apply (prop_free_vars _ A0 t).
  - (* Always *)
    specialize (prop_free_vars _ A0 t) as s0.
    case Ht: (t == t0); move/eqP: Ht => Ht.
    - (* t = t0 *)
      subst t0.
      apply (rem x s0).
    - (* t <> t0 *)
      apply s0.
  - (* AlwaysF' *)
    apply (prop_free_vars _ A0 t).
  - (* AlwaysP' *)
    apply (prop_free_vars _ A0 t).
  - (* ExistsF' *)
    apply (prop_free_vars _ A0 t).
  - (* ExistsP' *)
    apply (prop_free_vars _ A0 t).
  - (* Next *)
    apply (prop_free_vars _ A0 t).
  - (* Self *)
    apply (prop_free_vars _ A0 t).
Defined.

(* Extracts the rigid variables used in a term *)
Fixpoint prop_vars {C} (A : @prop C) (t : type) :=
  match A with
  | Atom a => term_vars a t
  | Conj A1 A2 => union (prop_vars A1 t) (prop_vars A2 t)
  | Neg A0 => prop_vars A0 t
  | Always _ _ A0 => prop_vars A0 t
  | AlwaysF' A0 => prop_vars A0 t
  | AlwaysP' A0 => prop_vars A0 t
  | ExistsF' A0 => prop_vars A0 t
  | ExistsP' A0 => prop_vars A0 t
  | Next A0 => prop_vars A0 t
  | Self A0 => prop_vars A0 t
  end.

(* Extracts the bound rigid variables used in a term *)
Definition prop_bound_vars {C} (A : @prop C) (t : type) :=
  filter (fun x => x \notin prop_free_vars A t) (prop_vars A t).

(* Generalizes a prop by universally quantifying all free variables *)
Definition generalize_prop {C} (A : @prop C) :=
  foldr (fun t A => foldr Always A (prop_free_vars A t)) A (prop_var_types A).

Definition always_subst {C tx}
(prop_subst : (forall t, @substitution C t) -> @prop C)
(s : forall t, @substitution C t)
(x : @rigid_var C tx) (A : @prop C) : @prop C.

  have x' : rigid_var tx.
    have p (y : rigid_var tx) : bool.
      have e : term tx.
        case (s _ y) => [e' | ].
        - (* Some e' *)
          by assumption.
        - (* None *)
          by exact: (Rigid y).
      pose es := (term_vars e tx).
      by exact: (x \in es).
    case (has p (filter (fun y => y != x) (prop_free_vars A tx))).
    - (* has *)
      have s' : forall t, @rigid_var C t -> option (@term C t).
      move=> ty; case H : (ty == tx); move/eqP: H => H.
      - (* ty == tx *)
        subst ty; move=> y; case (y == x).
        - (* y == x *)
          by exact: (Some (Rigid x)).
        - (* y != x *)
          by exact: (s _ y).
      - (* ty != tx *)
        move=> y; by exact: (s _ y).
      by exact: fresh_rigid_var (prop_free_vars (prop_subst s') tx).
    - (* doesn't *)
      by exact: x.

  (* Substitution to apply to the proposition A *)
  have s' : forall t, @rigid_var C t -> option (@term C t).
  move=> ty; case H : (ty == tx); move/eqP: H => H.
  - (* ty == tx *)
    subst ty; move=> y; case (y == x).
    - (* y == x *)
      by exact: (Some (Rigid x')).
    - (* y != x *)
      by exact: (s _ y).
  - (* ty != tx *)
    move=> y; by exact: (s _ y).

  by exact: (Always x' (prop_subst s')).
Defined.

(* Substitution of terms in place of rigid variables *)
Fixpoint prop_subst {C} (s : forall t, @substitution C t) (A : @prop C)
: @prop C.
  inversion A.
  - (* Atom *)
    exact: (Atom (term_subst s a)).
  - (* Conj *)
    exact: (Conj (prop_subst _ s A1) (prop_subst _ s A2)).
  - (* Neg *)
    exact: (Neg (prop_subst _ s A0)).
  - (* Always *)
    (* This is a hack; A0 is already applied to prop_subst to satisfy the
       fixpoint decreasing argument requirements.  However, always_subst still
       needs A0 to substitute over *)
    apply (always_subst (fun s => prop_subst C s A0) s x A0).
  - (* AlwaysF' *)
    exact: (AlwaysF' (prop_subst _ s A0)).
  - (* AlwaysP' *)
    exact: (AlwaysP' (prop_subst _ s A0)).
  - (* ExistsF' *)
    exact: (ExistsF' (prop_subst _ s A0)).
  - (* ExistsP' *)
    exact: (ExistsP' (prop_subst _ s A0)).
  - (* Next *)
    exact: (Next (prop_subst _ s A0)).
  - (* Self *)
    exact: (Self (prop_subst _ s A0)).
Defined.
