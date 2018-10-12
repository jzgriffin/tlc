From mathcomp.ssreflect
Require Import ssreflect eqtype seq.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Inductive type for performing a type-level mapping over a sequence *)
Inductive mapseq {T : Type} (f : T -> Type) : seq T -> Type :=
| MNil : mapseq f nil
| MCons x xs : f x -> mapseq f xs -> mapseq f (x :: xs).
