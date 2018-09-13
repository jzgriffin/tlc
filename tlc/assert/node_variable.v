From mathcomp.ssreflect
Require Import ssreflect eqtype ssrbool ssrnat seq path.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Inductive node_variable : Type :=
| NV : nat -> node_variable.

(* Equality *)
Section node_variable_eq.

  Definition eq_node_variable (x x' : node_variable) :=
    match x, x' with
    | NV n, NV n' => n == n'
    end.

  Lemma eq_node_variableP : Equality.axiom eq_node_variable.
  Proof.
    case=> n; case=> n'; rewrite /eq_node_variable /=; try by constructor.
    - (* V *)
      case Hn: (n == n');
        [move/eqP: Hn => ?; subst n' | constructor];
        last by case=> ?; subst n'; rewrite eqxx in Hn.
      by constructor.
  Qed.

  Canonical node_variable_eqMixin :=
    Eval hnf in EqMixin eq_node_variableP.
  Canonical node_variable_eqType :=
    Eval hnf in EqType node_variable node_variable_eqMixin.

End node_variable_eq.

(* Flexible variables *)
Notation Vfn := (NV 0).

(* Rigid variables *)
Notation Vrn := (NV 1).

(* Arbitrary variables *)
Definition first_node_var := NV 2.
Definition unwrap_node_var x := match x with NV n => n end.
Definition next_node_var x := NV (S (unwrap_node_var x)).
Definition fresh_node_var x xs :=
  let: ns := map unwrap_node_var xs in
  let: ns' := sort (fun a b => a < b) (undup ns) in
  let: xs' := map NV ns' in
  if x \in xs' then last first_node_var xs' else x.
Lemma fresh_node_var_unique x xs : ~(fresh_node_var x xs \in xs).
Proof.
  (* TODO *)
Admitted.
