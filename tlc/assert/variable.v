From mathcomp.ssreflect
Require Import ssreflect eqtype ssrbool ssrnat seq path.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Inductive variable : Type :=
| V : nat -> variable.

(* Equality *)
Section variable_eq.

  Definition eq_variable (x x' : variable) :=
    match x, x' with
    | V n, V n' => n == n'
    end.

  Lemma eq_variableP : Equality.axiom eq_variable.
  Proof.
    case=> n; case=> n'; rewrite /eq_variable /=; try by constructor.
    - (* V *)
      case Hn: (n == n');
        [move/eqP: Hn => ?; subst n' | constructor];
        last by case=> ?; subst n'; rewrite eqxx in Hn.
      by constructor.
  Qed.

  Canonical variable_eqMixin :=
    Eval hnf in EqMixin eq_variableP.
  Canonical variable_eqType :=
    Eval hnf in EqType variable variable_eqMixin.

End variable_eq.

(* Flexible variables *)
Notation Vfn := (V 0).
Notation Vfd := (V 1).
Notation Vfo := (V 2).
Notation Vfe := (V 3).
Notation Vfors := (V 4).
Notation Vfois := (V 5).
Notation Vfs := (V 6).
Notation Vfs' := (V 7).

(* Rigid variables *)
Notation Vrn := (V 8).
Notation Vrd := (V 9).
Notation Vro := (V 10).
Notation Vre := (V 11).
Notation Vrors := (V 12).
Notation Vrois := (V 13).
Notation Vrs := (V 14).
Notation Vri := (V 15).

(* Arbitrary variables *)
Definition first_var := V 16.
Definition unwrap_var x := match x with V n => n end.
Definition next_var x := V (S (unwrap_var x)).
Definition fresh_var x xs :=
  let: ns := map unwrap_var xs in
  let: ns' := sort (fun a b => a < b) (undup ns) in
  let: xs' := map V ns' in
  if x \in xs' then last first_var xs' else x.
Lemma fresh_var_unique x xs : ~(fresh_var x xs \in xs).
Proof.
  (* TODO *)
Admitted.
