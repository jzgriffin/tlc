From mathcomp.ssreflect
Require Import ssreflect eqtype ssrbool seq.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section eqseq.

  Variable T : eqType.
  Implicit Type s : seq T.

  Fixpoint union s1 s2 := undup (s1 ++ s2).
  Fixpoint intersection s1 s2 := [seq t <- undup s1 | t \in s2].
  Fixpoint extension s' s :=
    if s' == s then true else
    if s' is x :: t then extension t s else false.

End eqseq.

Notation "x <+> y" :=
  (union x y)
  (at level 30, right associativity).
Notation "x <*> y" :=
  (intersection x y)
  (at level 30, right associativity).
Notation "x <<< y" :=
  (extension x y)
  (at level 30, no associativity).

Section mapseq.

  Variable T : Type.

  Inductive mapseq (f : T -> Type) : seq T -> Type :=
  | mapnil : mapseq f nil
  | mapcons x xs : f x -> mapseq f xs -> mapseq f (x :: xs).

End mapseq.

Section optionseq.

  Variable T : Type.

  Definition osome (o : option T) :=
    if o is Some t then [:: t] else [::].

  Definition osomes (s : seq (option T)) :=
    flatten [seq osome o | o <- s].

  Definition owrap (s : seq T) :=
    [seq Some t | t <- s].

End optionseq.
