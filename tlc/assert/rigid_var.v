From mathcomp.ssreflect
Require Import ssreflect eqtype ssrbool ssrnat seq path.
From tlc.utility
Require Import indeq.
From tlc.assert
Require Import type.
From tlc.comp
Require Import component.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Named and typed rigid variables in the assertion language *)
Inductive rigid_var {C} : @type C -> Type :=
| RigidVar t (n : nat) : rigid_var t.

(* Equality *)
Section eq.

  Definition rigid_var_eq {C t} (x x' : @rigid_var C t) :=
    match x, x' with
    | RigidVar _ n, RigidVar _ n' => n == n'
    end.

  Lemma rigid_var_eqP {C t} : Equality.axiom (@rigid_var_eq C t).
  Proof.
    case=> ? n; case=> ? n'; indeq_auto.
    - (* RigidVar *) by indeq n n'.
  Qed.

  Canonical rigid_var_eqMixin {C t} :=
    EqMixin (@rigid_var_eqP C t).
  Canonical rigid_var_eqType {C t} :=
    Eval hnf in EqType (@rigid_var C t) (@rigid_var_eqMixin C t).

End eq.

(* Extracts the name of a rigid variable *)
Definition unwrap_rigid_var {C t} (x : @rigid_var C t) :=
  match x with
  | RigidVar _ s => s
  end.

(* Generating fresh rigid variables *)
Definition fresh_rigid_var {C t} (xs : seq (@rigid_var C t)) :=
  let: ns := undup [seq unwrap_rigid_var x | x <- xs] in
  let: ns' := sort gtn ns in
  let: n' := head 0 ns' in
  @RigidVar C t n'.
Lemma fresh_rigid_var_correct {C t} (xs : seq (@rigid_var C t)) :
  ~fresh_rigid_var xs \in xs.
Proof.
  (* TODO *)
Admitted.
