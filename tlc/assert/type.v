From mathcomp.ssreflect
Require Import ssreflect eqtype ssrbool ssrnat seq fintype.
From tlc.utility
Require Import indeq seq func variant lemmas.
From tlc.comp
Require Import p_event component flc.
From tlc.assert
Require Import scope orientation.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Types of terms in the assertion language *)
Inductive type {C : component} : Type :=
| Unit
| Func (t1 t2 : type)
| Product (t1 t2 : type)
| Sum (t1 t2 : type)
| List (t : type)
| Bool
| Nat
| Node
| Message
| Orientation
| FLRequest
| FLIndication
| IREvent
| OIEvent
| OREvent' (i : 'I_(size (or_events C)))
| IIEvent' (i : 'I_(size (ii_events C)))
| PEvent
| State.

Bind Scope tlc_type_scope with type.

(* Notations for building types *)
Notation "x -> y" :=
  (Func x y)
  : tlc_type_scope.
Notation "x * y" :=
  (Product x y)
  : tlc_type_scope.
Notation "x + y" :=
  (Sum x y)
  : tlc_type_scope.
Notation "[ x ]" :=
  (List x)
  : tlc_type_scope.

(* Equality *)
Section eq.

  Fixpoint type_eq {C} (t t' : @type C) :=
    match t, t' with
    | Unit, Unit => true
    | Func t1 t2, Func t1' t2' => type_eq t1 t1' && type_eq t2 t2'
    | Product t1 t2, Product t1' t2' => type_eq t1 t1' && type_eq t2 t2'
    | Sum t1 t2, Sum t1' t2' => type_eq t1 t1' && type_eq t2 t2'
    | List t1, List t1' => type_eq t1 t1'
    | Bool, Bool => true
    | Nat, Nat => true
    | Node, Node => true
    | Message, Message => true
    | Orientation, Orientation => true
    | FLRequest, FLRequest => true
    | FLIndication, FLIndication => true
    | IREvent, IREvent => true
    | OIEvent, OIEvent => true
    | OREvent' i1, OREvent' i2 => i1 == i2
    | IIEvent' i1, IIEvent' i2 => i1 == i2
    | State, State => true
    | _, _ => false
    end.

  Lemma type_eqP {C} : Equality.axiom (@type_eq C).
  Proof.
    (* TODO *)
  Admitted.

  Canonical type_eqMixin {C} :=
    EqMixin (@type_eqP C).
  Canonical type_eqType {C} :=
    Eval hnf in EqType (@type C) (@type_eqMixin C).

End eq.

(* Denotational semantics *)
Section denote.

  (* Maps a type to its concrete Type *)
  Fixpoint denote_type {C} (t : @type C) : eqType :=
    match t with
    | Unit => [eqType of unit]
    | Func t1 t2 => [eqType of denote_type t1 -> denote_type t2]
    | Product t1 t2 => [eqType of prod (denote_type t1) (denote_type t2)]
    | Sum t1 t2 => [eqType of sum (denote_type t1) (denote_type t2)]
    | List t => [eqType of seq (denote_type t)]
    | Bool => [eqType of bool]
    | Nat => [eqType of nat]
    | Node => node C
    | Message => message C
    | Orientation => [eqType of orientation]
    | FLRequest => [eqType of (@req_fl (node C) (message C))]
    | FLIndication => [eqType of (@ind_fl (node C) (message C))]
    | IREvent => ir_event C
    | OIEvent => oi_event C
    | OREvent' i => ith i
    | IIEvent' i => ith i
    | PEvent => [eqType of p_event]
    | State => state C
    end.

  Lemma denote_unit {C} :
    @denote_type C Unit = [eqType of unit].
  Proof. by []. Qed.

  Lemma denote_func {C} (t1 t2 : @type C) :
    denote_type (t1 -> t2) = [eqType of denote_type t1 -> denote_type t2].
  Proof. by []. Qed.

  Lemma denote_product {C} (t1 t2 : @type C) :
    denote_type (t1 * t2) = [eqType of prod (denote_type t1) (denote_type t2)].
  Proof. by []. Qed.

  Lemma denote_sum {C} (t1 t2 : @type C) :
    denote_type (t1 + t2) = [eqType of sum (denote_type t1) (denote_type t2)].
  Proof. by []. Qed.

  Lemma denote_list {C} (t : @type C) :
    denote_type [t] = [eqType of seq (denote_type t)].
  Proof. by []. Qed.

End denote.

(* Parametric types *)
Fixpoint Variant {C} (ts : seq (@type C)) : @type C :=
  match ts with
  | nil => Unit
  | t :: nil => t
  | t :: ts' => Sum t (Variant ts')
  end.

Lemma Variant_cons {C} (t : @type C) (ts : seq (@type C)) :
  ts <> nil ->
  Sum t (Variant ts) = Variant (t :: ts).
Proof.
  move=> H. case H': ts; last by [].
  by contradiction.
Qed.

Lemma denote_variant {C} (ts : seq (@type C)) :
  denote_type (Variant ts) = eqVariant [seq denote_type t | t <- ts].
Proof.
  elim Hts: ts => [ | t ts' IHts]; first by [].
  case Hts': ts' => [ | t' ts'']; first by [].
  rewrite -Variant_cons; last by [].
  rewrite -eqVariant_cons; last by [].
  by rewrite -Hts' denote_sum IHts Hts' //.
Qed.

(* Component types *)
Definition OREvents {C} : seq (@type C) :=
  [seq OREvent' i | i <- ord_enum (size (or_events C))].
Definition IIEvents {C} : seq (@type C) :=
  [seq IIEvent' i | i <- ord_enum (size (ii_events C))].
Definition OREvent {C} : @type C :=
  Variant OREvents.
Definition IIEvent {C} : @type C :=
  Variant IIEvents.

Lemma denote_or_events {C} :
  [seq @denote_type C t | t <- OREvents] = or_events C.
Proof.
  rewrite /OREvents /or_events map_map /denote_type.
  by exact: map_ith_ord_enum.
Qed.

Lemma denote_ii_events {C} :
  [seq @denote_type C t | t <- IIEvents] = ii_events C.
Proof.
  rewrite /IIEvents /ii_events map_map /denote_type.
  by exact: map_ith_ord_enum.
Qed.

Lemma denote_or_event {C} : @denote_type C OREvent = or_event C.
Proof.
  by rewrite /OREvent /or_event denote_variant denote_or_events.
Qed.

Lemma denote_ii_event {C} : @denote_type C IIEvent = ii_event C.
Proof.
  by rewrite /IIEvent /ii_event denote_variant denote_ii_events.
Qed.

(* Composite types *)
Definition Depth {C} : @type C :=
  [Nat].
Definition Event {C} : @type C :=
  IREvent + OIEvent + OREvent + IIEvent + PEvent.
Definition States {C} : @type C :=
  Node -> State.
