Require Import Coq.Lists.List.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Inductive tuple_map A (f : A -> Type) : list A -> Type :=
| TupleMapNil : tuple_map f nil
| TupleMapCons x xs : f x -> tuple_map f xs -> tuple_map f (x :: xs).
