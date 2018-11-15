Require Import Coq.Vectors.Vector.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import VectorNotations.

Fixpoint variant n (As : Vector.t Type n) : Type :=
  match As with
  | [] => unit
  | [A] => A
  | A :: As' => A + variant As'
  end.

Lemma variant_cons n (A : Type) (As : Vector.t Type n) :
  n > 0 -> variant (A :: As) = sum A (variant As).
Proof.
  destruct As as [ | A' As']; easy.
Qed.

(* Constructs a variant term inhabiting the i^th type *)
Fixpoint in_variant n (As : Vector.t Type n) i (x : As[@i]) {struct As} :
  variant As.
Proof.
Admitted. (* TODO *)
