Require Import mathcomp.ssreflect.seq.
Require Import mathcomp.ssreflect.ssreflect.
Require Import mathcomp.ssreflect.ssrfun.
Require Import tlc.utility.applicative.
Require Import tlc.utility.functor.
Require Import tlc.utility.monad.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Maps over the fsts in a sequence of pairs *)
Fixpoint map1 a b a' (f : a -> a') (ps : seq (a * b)) :=
  if ps is (x, y) :: ps' then (f x, y) :: map1 f ps' else nil.

(* Maps over the snds in a sequence of pairs *)
Fixpoint map2 a b b' (f : b -> b') (ps : seq (a * b)) :=
  if ps is (x, y) :: ps' then (x, f y) :: map2 f ps' else nil.

(* Functor instance for seq *)
Instance seq_functor : Functor seq := {
  map a b (f : a -> b) :=
    fix m xs :=
      match xs with
      | [::] => [::]
      | x :: xs => f x :: m xs
      end;
}.
Proof.
  - by move=> a; elim=> [| x xs IHxs] //=; rewrite IHxs.
  - by move=> a b c f g; elim=> [| x xs IHxs] //=; rewrite IHxs.
Defined.
