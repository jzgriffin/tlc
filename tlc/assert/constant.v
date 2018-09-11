From mathcomp.ssreflect
Require Import ssreflect eqtype ssrbool ssrnat.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Inductive constant : Type :=
| Cnat : nat -> constant
| Cnil
| Creq_ev
| Cind_ev
| Cper_ev
| Cper
| Cnat_set
| Ccorrect_set.

(* Equality *)
Section constant_eq.

  Definition eq_constant (c c' : constant) :=
    match c, c' with
    | Cnat n, Cnat n' => n == n'
    | Cnil, Cnil => true
    | Creq_ev, Creq_ev => true
    | Cind_ev, Cind_ev => true
    | Cper_ev, Cper_ev => true
    | Cper, Cper => true
    | Cnat_set, Cnat_set => true
    | Ccorrect_set, Ccorrect_set => true
    | _, _ => false
    end.

  Lemma eq_constantP : Equality.axiom eq_constant.
  Proof.
    case=> [n | ]; case=> [n' | ]; rewrite /eq_constant /=;
      try by constructor.
    - (* Cnat *)
      case Hn: (n == n');
        [move/eqP: Hn => ?; subst n' | constructor];
        last by case=> ?; subst n'; rewrite eqxx in Hn.
      by constructor.
  Qed.

  Canonical constant_eqMixin :=
    Eval hnf in EqMixin eq_constantP.
  Canonical constant_eqType :=
    Eval hnf in EqType constant constant_eqMixin.

End constant_eq.
