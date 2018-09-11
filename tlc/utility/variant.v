From mathcomp.ssreflect
Require Import ssreflect eqtype ssrbool seq.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section variant.

  Fixpoint variant (types : seq Type) : Type :=
    match types with
    | nil => unit
    | x :: t => if t is nil then x else sum x (variant t)
    end.

End variant.
