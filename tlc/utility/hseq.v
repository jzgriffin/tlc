From mathcomp.ssreflect
Require Import ssreflect seq.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section hseq.

  Variable A : Type.
  Variable B : A -> Type.

  Inductive hseq : seq A -> Type :=
  | HNil : hseq nil
  | HCons x xs : B x -> hseq xs -> hseq (x :: xs).

  Variable x : A.

  Inductive member : seq A -> Type :=
  | HFirst xs : member (x :: xs)
  | HNext y xs : member xs -> member (y :: xs).

  Fixpoint hget xs (mxs : hseq xs) : member xs -> B x :=
    match mxs with
    | HNil => fun m =>
      match m in member xs'
      return
        match xs' with
        | nil => B x
        | _ :: _ => unit
        end
      with
      | HFirst _ => tt
      | HNext _ _ _ => tt
      end
    | HCons _ _ y mxs' => fun m =>
      match m in member xs'
      return
        match xs' with
        | nil => Empty_set
        | x' :: xs'' => B x' -> (member xs'' -> B x) -> B x
        end
      with
      | HFirst _ => fun z _ => z
      | HNext _ _ m' => fun _ gmxs' => gmxs' m'
      end y (hget mxs')
    end.

End hseq.

Arguments HNil [A B].
Arguments HCons [A B x xs].

Arguments HFirst [A x xs].
Arguments HNext [A x y xs].
