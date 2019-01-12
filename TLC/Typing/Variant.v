Require Import TLC.Typing.Type.
Require Import Coq.Lists.List.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Variadic sum type *)
Section variant.

  Import ListNotations.

  Fixpoint TVariant (ts : list type) : type :=
    match ts with
    | [] => TUnit
    | [t] => t
    | t :: ts' => t + TVariant ts'
    end.

End variant.
