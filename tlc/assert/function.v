From mathcomp.ssreflect
Require Import ssreflect eqtype ssrbool.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Inductive function : Type :=
| Fcons.

(* Equality *)
Section function_eq.

  Definition eq_function (f f' : function) :=
    match f, f' with
    | Fcons, Fcons => true
    end.

  Lemma eq_functionP : Equality.axiom eq_function.
  Proof.
    case; case; rewrite /eq_function /=; by constructor.
  Qed.

  Canonical function_eqMixin :=
    Eval hnf in EqMixin eq_functionP.
  Canonical function_eqType :=
    Eval hnf in EqType function function_eqMixin.

End function_eq.
