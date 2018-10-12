From Coq.Lists
Require Import List.
From mathcomp.ssreflect
Require Import ssreflect eqtype ssrbool ssrnat seq fintype.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Sequences of eqTypes *)
Section eqseq.

  Variable T : eqType.
  Implicit Type x : T.
  Implicit Type s : seq T.

  Fixpoint union s1 s2 := undup (s1 ++ s2).
  Fixpoint intersection s1 s2 := [seq t <- undup s1 | t \in s2].

  (* Predicate: s' is an extension of s <-> s is a suffix of s' *)
  Fixpoint extension s' s :=
    if s' == s then true else
    if s' is x :: t then extension t s else false.

  Lemma inP x s : reflect (In x s) (x \in s).
    elim: s => [ | x' s' IHs]; first by rewrite /= in_nil; constructor.
    rewrite /= in_cons. case Hx: (x' == x).
    - (* x' == x *)
      move/eqP: Hx => Hx; subst x'; rewrite eqxx; constructor; by left.
    - (* x' != x *)
      rewrite eq_sym in Hx. rewrite Hx orFb.
      rewrite eq_sym in Hx. move/eqP: Hx => Hx.
      (* TODO: This requires the excluded middle.  Find another way. *)
      have todo P Q : ~P -> (P \/ Q) = Q by admit.
      rewrite todo; by [].
  Admitted.

End eqseq.

Arguments union {T}.
Arguments intersection {T}.
Arguments extension {T}.

Notation "x <+> y" :=
  (union x y)
  (at level 30, right associativity).
Notation "x <*> y" :=
  (intersection x y)
  (at level 30, right associativity).
Notation "x <<< y" :=
  (extension x y)
  (at level 30, no associativity).

(* Dependent nth element *)
Fixpoint ith T (s : seq T) (i : 'I_(size s)) : T.
  case: i;
  elim: s => [ | t s IHs] n Hn; first by [];
  case: n Hn => [ | n] Hn; first by [].
  have SltnS x y: (x.+1 < y.+1 -> x < y) by [].
  rewrite /= in Hn; apply SltnS in Hn.
  apply (ith T s (Ordinal Hn)).
Defined.

Lemma ith0 T (t : T) (ts : seq T) (H : 0 < size (t :: ts)) :
  ith (Ordinal H) = t.
Proof.
  by [].
Qed.

Lemma ith_map T T' (f : T -> T') (s : seq T) (s' : seq T')
(i : 'I_(size s)) (i' : 'I_(size s')) (H : s' = [seq f x | x <- s])
: f (ith i) = ith i'.
Admitted.

Lemma map_ith_ord_enum T (s : seq T) :
  [seq ith i | i <- ord_enum (size s)] = s.
Proof.
  elim: s => [ | x s' IHs] //=; admit. (* TODO *)
Admitted.

(* Finite successor *)
Definition fsucc n (i : 'I_n) : 'I_n.+1.
  case: i => m E; apply ltnW in E; rewrite -ltnS in E.
  exact: (Ordinal E).
Defined.

(* Dependent index of element *)
Fixpoint findex (T : eqType) (x : T) (s : seq T) (H : In x s) {struct s}
: 'I_(size s).
  elim Hs: s H => [ | x' s' IHs] H; first by [].
  case Hx: (x == x').
  - (* x == x' *)
    have E : (0 < size (x' :: s')) by [];
    by exact: (Ordinal E).
  - (* x != x' *)
    move/inP: H; rewrite in_cons Hx orFb; move/inP=> H.
    specialize (findex _ x s' H); apply fsucc.
    by exact: findex.
Defined.
