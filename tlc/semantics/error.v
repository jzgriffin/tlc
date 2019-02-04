Require Import tlc.syntax.pattern.
Require Import tlc.syntax.term.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Kinds of errors produced during semantic operations *)
Inductive error :=
(* Opening *)
| EParameter (t : term)
(* Pattern matching *)
| EMatch (p : pattern) (t : term)
(* Evaluation *)
| EFailure
| EBoolean (t : term)
| ENatural (t : term)
| EList (t : term)
| EFuel (t : term).
