From mathcomp.ssreflect
Require Import ssreflect eqtype ssrbool.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Equality *)
Section eq.

  Definition func_eq {d r} (f f' : d -> r) := false.

  Lemma func_eqP {d r} : Equality.axiom (@func_eq d r).
  Proof.
    (* TODO *)
  Admitted.

  Canonical func_eqMixin {d r} :=
    EqMixin (@func_eqP d r).
  Canonical func_eqType {d r} :=
    Eval hnf in EqType (d -> r) (@func_eqMixin d r).

End eq.
