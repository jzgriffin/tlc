From mathcomp.ssreflect
Require Import ssreflect eqtype seq.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Type of periodic events *)
Inductive p_event : Type :=
| per.

(* Equality *)
Section eq.

  Fixpoint p_event_eq (p p' : p_event) :=
    match p, p' with
    | per, per => true
    end.

  Lemma p_event_eqP : Equality.axiom p_event_eq.
  Proof.
    case; case; rewrite //=; by constructor.
  Qed.

  Canonical p_event_eqMixin :=
    EqMixin p_event_eqP.
  Canonical p_event_eqType :=
    Eval hnf in EqType p_event p_event_eqMixin.

End eq.