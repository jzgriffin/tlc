From mathcomp.ssreflect
Require Import ssreflect eqtype ssrbool seq ssrnat fintype.
From tlc.utility
Require Import seq lemmas.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Right-associative sum types parameterized by sequences of types *)

Fixpoint variant (ts : seq Type) : Type :=
  match ts with
  | nil => unit
  | t :: nil => t
  | t :: ts' => sum t (variant ts')
  end.

Fixpoint eqVariant (ts : seq eqType) : eqType :=
  match ts with
  | nil => [eqType of unit]
  | t :: nil => t
  | t :: ts' => [eqType of sum t (eqVariant ts')]
  end.

Lemma variant_cons (t : Type) (ts : seq Type) :
  ts <> nil ->
  sum t (variant ts) = variant (t :: ts).
Proof.
  move=> H. case H': ts; last by [].
  by contradiction.
Qed.

Lemma eqVariant_cons (t : eqType) (ts : seq eqType) :
  ts <> nil ->
  [eqType of sum t (eqVariant ts)] = eqVariant (t :: ts).
Proof.
  move=> H. case H': ts; last by [].
  by contradiction.
Qed.

Fixpoint ini (ts : seq Type) (i : 'I_(size ts)) : ith i -> variant ts.
  case: ts i => [ | t ts] [i H];
  rewrite /nat_of_ord => x //;
  case Hts: ts => [ | t' ts'].
  - (* ts = [::] *)
    subst ts.
    assert (H' := H); move: H'; rewrite ltnS leqn0 /=; move/eqP=> Hi; subst i.
    move: x; rewrite //.
  - (* ts = t' :: ts' *)
    case Hi: i => [ | i']; subst i; first by apply (inl x).
    rewrite -variant_cons; last by [].
    rewrite -Hts; exact: (inr (ini ts _ x)).
Defined.

Fixpoint eq_ini (ts : seq eqType) (i : 'I_(size ts)) : ith i -> eqVariant ts.
  case: ts i => [ | t ts] [i H];
  rewrite /nat_of_ord => x //;
  case Hts: ts => [ | t' ts'].
  - (* ts = [::] *)
    subst ts.
    assert (H' := H); move: H'; rewrite ltnS leqn0 /=; move/eqP=> Hi; subst i.
    move: x; rewrite //.
  - (* ts = t' :: ts' *)
    case Hi: i => [ | i']; subst i; first by apply (inl x).
    rewrite -eqVariant_cons; last by [].
    rewrite -Hts; exact: (inr (eq_ini ts _ x)).
Defined.
