From mathcomp.ssreflect
Require Import ssreflect eqtype ssrbool ssrnat seq path.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Inductive message_variable : Type :=
| MV : nat -> message_variable.

(* Equality *)
Section message_variable_eq.

  Definition eq_message_variable (x x' : message_variable) :=
    match x, x' with
    | MV n, MV n' => n == n'
    end.

  Lemma eq_message_variableP : Equality.axiom eq_message_variable.
  Proof.
    case=> n; case=> n'; rewrite /eq_message_variable /=; try by constructor.
    - (* V *)
      case Hn: (n == n');
        [move/eqP: Hn => ?; subst n' | constructor];
        last by case=> ?; subst n'; rewrite eqxx in Hn.
      by constructor.
  Qed.

  Canonical message_variable_eqMixin :=
    Eval hnf in EqMixin eq_message_variableP.
  Canonical message_variable_eqType :=
    Eval hnf in EqType message_variable message_variable_eqMixin.

End message_variable_eq.

(* Rigid variables *)
Notation Vrm := (MV 0).

(* Arbitrary variables *)
Definition first_message_var := MV 1.
Definition unwrap_message_var x := match x with MV n => n end.
Definition next_message_var x := MV (S (unwrap_message_var x)).
Definition fresh_message_var x xs :=
  let: ns := map unwrap_message_var xs in
  let: ns' := sort (fun a b => a < b) (undup ns) in
  let: xs' := map MV ns' in
  if x \in xs' then last first_message_var xs' else x.
Lemma fresh_message_var_unique x xs : ~(fresh_message_var x xs \in xs).
Proof.
  (* TODO *)
Admitted.
