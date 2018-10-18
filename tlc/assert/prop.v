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

(* Inductive type for building first-order temporal propositions *)
Inductive prop {C} : Type :=
| Atom (a : @atom C)
| Not (p : prop)
| Or (p q : prop)
| Forall {t} (x : @rigid_var C t) (p : prop)
| Until' (p q : prop)
| Since' (p q : prop)
| Self (p : prop).

Bind Scope tlc_core_scope with prop.

Coercion Atom : atom >-> prop.

(* Notations for true and false propositions *)
Notation True' := (Atom (@Const _ Bool true))
  (only parsing).
Notation False' := (Atom (@Const _ Bool false))
  (only parsing).

(* Basic notation for building propositions *)
Notation "~ p" := (Not p)
  (at level 75, right associativity) : tlc_core_scope.
Notation "p \/ q" := (Or p q)
  (at level 85, right associativity) : tlc_core_scope.
Notation "'forall:' x , p" := (@Forall _ _ x p)
  (at level 65, right associativity) : tlc_core_scope.
Notation "p 'until^' q" := (Until' p q)
  (at level 65, right associativity) : tlc_core_scope.
Notation "p 'since^' q" := (Since' p q)
  (at level 65, right associativity) : tlc_core_scope.
Notation "'self:' p" := (Self p)
  (at level 65, right associativity) : tlc_core_scope.

(* Syntactic sugar for first-order logic *)
Definition And {C} (p q : @prop C) : @prop C := ~(~p \/ ~q).
Notation "p /\ q" := (And p q)
  (at level 80, right associativity) : tlc_core_scope.
Definition If {C} (p q : @prop C) : @prop C := ~p \/ q.
Notation "p -> q" := (If p q)
  (at level 99, right associativity, q at level 200) : tlc_core_scope.
Definition Iff {C} (p q : @prop C) : @prop C := p -> q \/ q -> p.
Notation "p <-> q" := (Iff p q)
  (at level 95, no associativity) : tlc_core_scope.
Definition Exists {C t} (x : @rigid_var C t) (p : @prop C) : @prop C :=
  ~forall: x, ~p.
Notation "'exists:' x , p" := (@Exists _ _ x p)
  (at level 65, right associativity) : tlc_core_scope.

(* Syntactic sugar for temporal logic *)
Definition Eventually' {C} (p : @prop C) : @prop C := True' until^ p.
Notation "'eventually^:' p" := (Eventually' p)
  (at level 65, right associativity) : tlc_core_scope.
Definition Once' {C} (p : @prop C) : @prop C := True' since^ p.
Notation "'once^:' p" := (Once' p)
  (at level 65, right associativity) : tlc_core_scope.
Definition Henceforth' {C} (p : @prop C) : @prop C := ~eventually^: ~p.
Notation "'henceforth^:' p" := (Henceforth' p)
  (at level 65, right associativity) : tlc_core_scope.
Definition AlwaysBeen' {C} (p : @prop C) : @prop C := ~once^: ~p.
Notation "'alwaysbeen^:' p" := (AlwaysBeen' p)
  (at level 65, right associativity) : tlc_core_scope.
Definition Unless' {C} (p q : @prop C) : @prop C :=
  (henceforth^: p) \/ (p until^ q).
Notation "p 'unless^' q" :=
  (Unless' p q)
  (at level 65, right associativity) : tlc_core_scope.
Definition BackTo' {C} (p q : @prop C) : @prop C :=
  (alwaysbeen^: p) \/ (p since^ q).
Notation "p 'backto^' q" :=
  (BackTo' p q)
  (at level 65, right associativity) : tlc_core_scope.
Definition Next {C} (p : @prop C) : @prop C := False' until^ p.
Notation "'next:' p" := (Next p)
  (at level 65, right associativity) : tlc_core_scope.
Definition Previous {C} (p : @prop C) : @prop C := False' since^ p.
Notation "'previous:' p" := (Previous p)
  (at level 65, right associativity) : tlc_core_scope.
Definition WeakPrevious {C} (p : @prop C) : @prop C := ~previous: ~p.
Notation "'previous~:' p" := (WeakPrevious p)
  (at level 65, right associativity) : tlc_core_scope.
Definition Henceforth {C} (p : @prop C) : @prop C := p /\ henceforth^: p.
Notation "'henceforth:' p" := (Henceforth p)
  (at level 65, right associativity) : tlc_core_scope.
Definition AlwaysBeen {C} (p : @prop C) : @prop C := p /\ alwaysbeen^: p.
Notation "'alwaysbeen:' p" := (AlwaysBeen p)
  (at level 65, right associativity) : tlc_core_scope.
Definition Eventually {C} (p : @prop C) : @prop C := p \/ eventually^: p.
Notation "'eventually:' p" := (Eventually p)
  (at level 65, right associativity) : tlc_core_scope.
Definition Once {C} (p : @prop C) : @prop C := p \/ once^: p.
Notation "'once:' p" := (Once p)
  (at level 65, right associativity) : tlc_core_scope.
Definition Until {C} (p q : @prop C) : @prop C := q \/ (p /\ (p until^ q)).
Notation "p 'until' q" := (Until p q)
  (at level 65, right associativity) : tlc_core_scope.
Definition Since {C} (p q : @prop C) : @prop C := q \/ (p /\ (p since^ q)).
Notation "p 'since' q" := (Since p q)
  (at level 65, right associativity) : tlc_core_scope.
Definition Unless {C} (p q : @prop C) : @prop C := q \/ (p /\ (p unless^ q)).
Notation "p 'unless' q" := (Unless p q)
  (at level 65, right associativity) : tlc_core_scope.
Definition BackTo {C} (p q : @prop C) : @prop C := q \/ (p /\ (p backto^ q)).
Notation "p 'backto' q" := (BackTo p q)
  (at level 65, right associativity) : tlc_core_scope.

(* Additional syntactic sugar *)
Definition Entails {C} (p q : @prop C) : @prop C := (henceforth: p) -> q.
Notation "p =>> q" := (Entails p q)
  (at level 98, right associativity) : tlc_core_scope.
Definition Congruent {C} (p q : @prop C) : @prop C := (p =>> q) /\ (q =>> p).
Notation "p <=> q" := (Congruent p q)
  (at level 98, right associativity) : tlc_core_scope.
Definition LeadsTo {C} (p q : @prop C) : @prop C := p =>> eventually: q.
Notation "p ~> q" := (LeadsTo p q)
  (at level 97, right associativity) : tlc_core_scope.
Definition PrecededBy {C} (p q : @prop C) : @prop C := p =>> once: q.
Notation "p <~ q" := (PrecededBy p q)
  (at level 97, right associativity) : tlc_core_scope.

(* Extracts the types of rigid variable used in a prop *)
Fixpoint prop_var_types {C} (p : @prop C) :=
  match p with
  | Atom a => term_var_types a
  | Not q => prop_var_types q
  | Or q r => union (prop_var_types q) (prop_var_types r)
  | Forall _ _ q => prop_var_types q
  | Until' q r => union (prop_var_types q) (prop_var_types r)
  | Since' q r => union (prop_var_types q) (prop_var_types r)
  | Self q => prop_var_types q
  end.

(* Extracts the free rigid variables used in a prop *)
Fixpoint prop_free_vars {C} (p : @prop C) (t : type) : seq (@rigid_var C t).
  case: p => [a | q | q r | tx x q | q r | q r | q].
  - (* Atom *)
    by exact: (@term_vars _ _ a t).
  - (* Not *)
    by exact: (prop_free_vars _ q t).
  - (* Or *)
    by exact: (union (prop_free_vars _ q t) (prop_free_vars _ r t)).
  - (* Forall *)
    specialize (prop_free_vars _ q t) as s.
    case Ht: (t == tx); move/eqP: Ht => Ht.
    - (* t = tx *)
      subst tx; by exact: (rem x s).
    - (* t <> tx *)
      by exact: s.
  - (* Until' *)
    by exact: (union (prop_free_vars _ q t) (prop_free_vars _ r t)).
  - (* Since' *)
    by exact: (union (prop_free_vars _ q t) (prop_free_vars _ r t)).
  - (* Self *)
    by exact: (prop_free_vars _ q t).
Defined.

(* Extracts the rigid variables used in a term *)
Fixpoint prop_vars {C} (p : @prop C) (t : type) : seq (@rigid_var C t).
  case: p => [a | q | q r | tx x q | q r | q r | q].
  - (* Atom *)
    by exact: (@term_vars _ _ a t).
  - (* Not *)
    by exact: (prop_vars _ q t).
  - (* Or *)
    by exact: (union (prop_vars _ q t) (prop_vars _ r t)).
  - (* Forall *)
    specialize (prop_vars _ q t) as s.
    case Ht: (t == tx); move/eqP: Ht => Ht.
    - (* t = tx *)
      subst tx; by exact: (undup (x :: s)).
    - (* t <> tx *)
      by exact: s.
  - (* Until' *)
    by exact: (union (prop_vars _ q t) (prop_vars _ r t)).
  - (* Since' *)
    by exact: (union (prop_vars _ q t) (prop_vars _ r t)).
  - (* Self *)
    by exact: (prop_vars _ q t).
Defined.

(* Extracts the bound rigid variables used in a term *)
Definition prop_bound_vars {C} (p : @prop C) (t : type) :=
  filter (fun x => x \notin prop_free_vars p t) (prop_vars p t).

(* Generalizes a prop by universally quantifying all free variables *)
Definition generalize_prop {C} (p : @prop C) :=
  foldr (fun t p => foldr Forall p (prop_free_vars p t)) p (prop_var_types p).

Definition forall_subst {C tx}
(prop_subst : (forall t, @substitution C t) -> @prop C)
(s : forall t, @substitution C t)
(x : @rigid_var C tx) (p : @prop C) : @prop C.
  have x' : rigid_var tx.
    have f (y : rigid_var tx) : bool.
      have e : term tx.
        case (s _ y) => [e' | ].
        - (* Some e' *)
          by assumption.
        - (* None *)
          by exact: (Rigid y).
      pose es := (term_vars e tx).
      by exact: (x \in es).
    case (has f (filter (fun y => y != x) (prop_free_vars p tx))).
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

  (* Substitution to apply to the proposition p *)
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

  by exact: (Forall x' (prop_subst s')).
Defined.

(* Substitution of terms in place of rigid variables *)
Fixpoint prop_subst {C} (s : forall t, @substitution C t) (p : @prop C)
: @prop C.
  case: p => [a | q | q r | tx x q | q r | q r | q].
  - (* Atom *)
    by exact: (Atom (term_subst s a)).
  - (* Not *)
    by exact: (Not (prop_subst _ s q)).
  - (* Or *)
    by exact: (Or (prop_subst _ s q) (prop_subst _ s r)).
  - (* Forall *)
    (* This is a hack; q is already applied to prop_subst to satisfy the
       fixpoint decreasing argument requirements.  However, forall_subst still
       needs q to substitute over *)
    by exact: (forall_subst (fun s => prop_subst C s q) s x q).
  - (* Until' *)
    by exact: (Until' (prop_subst _ s q) (prop_subst _ s r)).
  - (* Since' *)
    by exact: (Since' (prop_subst _ s q) (prop_subst _ s r)).
  - (* Self *)
    by exact: (Self (prop_subst _ s q)).
Defined.
