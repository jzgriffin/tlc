From mathcomp.ssreflect
Require Import ssreflect eqtype ssrbool.

Require Import term.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Inductive predicate : Type :=
| Peq
| Pin
| Pcorrect.

(* Equality *)
Section predicate_eq.

  Definition eq_predicate (c c' : predicate) :=
    match c, c' with
    | Peq, Peq => true
    | Pin, Pin => true
    | Pcorrect, Pcorrect => true
    | _, _ => false
    end.

  Lemma eq_predicateP : Equality.axiom eq_predicate.
  Proof.
    case; case; rewrite /eq_predicate /=; by constructor.
  Qed.

  Canonical predicate_eqMixin :=
    Eval hnf in EqMixin eq_predicateP.
  Canonical predicate_eqType :=
    Eval hnf in EqType predicate predicate_eqMixin.

End predicate_eq.
