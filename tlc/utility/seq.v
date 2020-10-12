(* TLC in Coq
 *
 * Module: tlc.utility.seq
 * Purpose: Definitions, lemmas, tactics, and typeclasses related to seq.
 *)

Require Import mathcomp.ssreflect.eqtype.
Require Import mathcomp.ssreflect.seq.
Require Import mathcomp.ssreflect.ssrbool.
Require Import mathcomp.ssreflect.ssreflect.
Require Import mathcomp.ssreflect.ssrfun.
Require Import mathcomp.ssreflect.ssrnat.
Require Import tlc.utility.functor.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma cat_foldr_cons A (xs1 xs2 : seq A) :
  xs1 ++ xs2 = foldr cons xs2 xs1.
Proof.
  by elim: xs1 => [| x1 xs1] //= <-.
Qed.

(* Compute the union of two lists *)
Definition union (A : eqType) (xs1 xs2 : seq A) :=
  undup (xs1 ++ xs2).

(* Compute the union of the single element x and list ys *)
Definition union1 (A : eqType) (x : A) (ys : seq A) :=
  union [:: x] ys.

(* Compute the union of sets xss *)
Definition big_union (A : eqType) (xss : seq (seq A)) :=
  foldr (@union _) [::] xss.

(* Determine whether every element of xs is an element of ys *)
Definition subset (A : eqType) (xs ys : seq A) :=
  all (fun x => x \in ys) xs.

Lemma subsets0 (A : eqType) (xs : seq A) :
  subset xs [::] -> xs = [::].
Proof.
  by elim: xs => [| x xs IHxs].
Qed.

Lemma subset_consr (A : eqType) x (xs' xs : seq A) :
  subset xs' xs ->
  subset xs' (x :: xs).
Proof.
  elim: xs' => [| x' xs' IH] //= /andP [Hm' Hs].
  apply/andP; split; first by rewrite in_cons; apply/orP; right.
  by apply: IH Hs.
Qed.

Lemma subsetxx (A : eqType) (xs : seq A) :
  subset xs xs.
Proof.
  elim: xs => [| x xs IH] //=.
  apply/andP; split; first by rewrite in_cons; apply/orP; left.
  by exact: subset_consr.
Qed.

Lemma subset_catl (A : eqType) (xs'1 xs'2 xs : seq A) :
  subset (xs'1 ++ xs'2) xs = subset xs'1 xs && subset xs'2 xs.
Proof.
  by elim: xs'1 => [| x1 xs'1] //= ->; rewrite andbA.
Qed.

Lemma subset_catrl (A : eqType) (xs1 xs2 : seq A) :
  subset xs1 (xs1 ++ xs2).
Proof.
  elim: xs1 => [| x xs1 IH] //=.
  apply/andP; split; first by rewrite in_cons; apply/orP; left.
  by exact: subset_consr.
Qed.

Lemma subset_catrr (A : eqType) (xs1 xs2 : seq A) :
  subset xs2 (xs1 ++ xs2).
Proof.
  elim: xs1 => [| x xs1 IH] //=; first by exact: subsetxx.
  by exact: subset_consr.
Qed.

Lemma subset_mem (A : eqType) x (xs1 xs2 : seq A) :
  subset xs1 xs2 ->
  x \in xs1 ->
  x \in xs2.
Proof.
  elim: xs1 => [| x' xs1 IH] //= /andP [Hm' Hs] Hm.
  case: (x == x') / eqP => E; first by subst.
  by rewrite in_cons in Hm; move/orP: Hm => [/eqP /E | Hm];
    last by apply: IH Hs Hm.
Qed.

Lemma subsetT (A : eqType) (xs1 xs2 xs3 : seq A) :
  subset xs1 xs2 ->
  subset xs2 xs3 ->
  subset xs1 xs3.
Proof.
  elim: xs1 => [| x xs1 IH] //= /andP [H2 H12] H23.
  apply/andP; split; last by apply: IH H12 H23.
  by apply subset_mem with (xs1 := xs2).
Qed.

(* Determine whether two lists have the same elements, regardless of ordering
 * and repetition
 *)
Definition set_eq (A : eqType) (xs1 xs2 : seq A) :=
  subset xs1 xs2 && subset xs2 xs1.

(* Determine whether xs' is an extension of xs
 * xs' is an extension if xs iff xs is a suffix of xs'
 *)
Fixpoint extension (A : eqType) (xs' xs : seq A) :=
  if xs' == xs then true else
  if xs' is x :: xs' then extension xs' xs else false.

(* If one element is in a list and another is not, those elements must not be
 * equal to one another
 *)
Lemma mem_neq (A : eqType) (x y : A) (xs : seq A) :
  y \in xs ->
  x \notin xs ->
  x != y.
Proof.
  elim: xs => //= x' xs IHxs; rewrite !in_cons;
  move/orP => [Hy | Hy]; move/norP => [Hx_eq Hx_mem].
  - by move/eqP: Hy => ->.
  - by exact: IHxs Hy Hx_mem.
Qed.

(* Automatically simplify or resolve goals involving seq membership *)
Ltac auto_mem := rewrite in_cons; apply/orP; (try by left); right.
Ltac auto_mem_conj :=
  by repeat match goal with
  | |- is_true ((_ \in _) && _) =>
    apply/andP; split
  | |- is_true (_ \in _) => repeat auto_mem
  end.

(* Functor instance for seq *)
#[refine]
Instance seq_functor : Functor seq := {
  map A B (f : A -> B) :=
    fix m xs :=
      match xs with
      | [::] => [::]
      | x :: xs => f x :: m xs
      end;
}.
Proof.
  (* map_id *)
  {
    by move=> ?; elim=> [| x xs ->] //.
  }

  (* map_comp *)
  {
    by move=> ?????; elim=> [| x xs ->] //.
  }
Defined.

(* Select the i'th element from seq xs, returning None if i is out of bounds *)
Fixpoint onth A (xs : seq A) i := 
  match xs, i with
  | x :: _, 0 => Some x
  | _ :: xs, i.+1 => onth xs i
  | _, _ => None
  end.
