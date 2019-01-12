Require Import Coq.Lists.List.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Variadic sum type *)
Section variant.

  Import ListNotations.

  Fixpoint variant (Ts : list Type) : Type :=
    match Ts with
    | [] => unit
    | [T] => T
    | T :: Ts' => T + variant Ts'
    end.

End variant.
