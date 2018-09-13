From mathcomp.ssreflect
Require Import ssreflect eqtype ssrbool ssrnat seq path.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Inductive general_variable : Type :=
| GV : nat -> general_variable.

(* Equality *)
Section general_variable_eq.

  Definition eq_general_variable (x x' : general_variable) :=
    match x, x' with
    | GV n, GV n' => n == n'
    end.

  Lemma eq_general_variableP : Equality.axiom eq_general_variable.
  Proof.
    case=> n; case=> n'; rewrite /eq_general_variable /=; try by constructor.
    - (* V *)
      case Hn: (n == n');
        [move/eqP: Hn => ?; subst n' | constructor];
        last by case=> ?; subst n'; rewrite eqxx in Hn.
      by constructor.
  Qed.

  Canonical general_variable_eqMixin :=
    Eval hnf in EqMixin eq_general_variableP.
  Canonical general_variable_eqType :=
    Eval hnf in EqType general_variable general_variable_eqMixin.

End general_variable_eq.

(* Flexible variables *)
Notation Vfd := (GV 0).
Notation Vfo := (GV 1).
Notation Vfe := (GV 2).
Notation Vfors := (GV 3).
Notation Vfois := (GV 4).
Notation Vfs := (GV 5).
Notation Vfs' := (GV 6).

(* Rigid variables *)
Notation Vrd := (GV 7).
Notation Vro := (GV 8).
Notation Vre := (GV 9).
Notation Vrors := (GV 10).
Notation Vrois := (GV 11).
Notation Vrs := (GV 12).
Notation Vri := (GV 13).

(* Arbitrary variables *)
Definition first_general_var := GV 14.
Definition unwrap_general_var x := match x with GV n => n end.
Definition next_general_var x := GV (S (unwrap_general_var x)).
Definition fresh_general_var x xs :=
  let: ns := map unwrap_general_var xs in
  let: ns' := sort (fun a b => a < b) (undup ns) in
  let: xs' := map GV ns' in
  if x \in xs' then last first_general_var xs' else x.
Lemma fresh_general_var_unique x xs : ~(fresh_general_var x xs \in xs).
Proof.
  (* TODO *)
Admitted.
