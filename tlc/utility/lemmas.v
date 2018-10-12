From mathcomp.ssreflect
Require Import ssreflect eqtype ssrbool ssrnat div fintype seq.
From tlc.utility
Require Import seq.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma SltnS n m : n.+1 < m.+1 -> n < m.
Proof.
  by [].
Qed.

Lemma ord_mod (n m : nat) : m > 0 -> 'I_m.
  move=> Hm.
  have H: (n %% m < m) by rewrite ltn_mod.
  exact: (Ordinal H).
Qed.

Lemma map_map T1 T2 T3 (f1 : T1 -> T2) (f2 : T2 -> T3) s :
  map f2 (map f1 s) = map (fun x => f2 (f1 x)) s.
Proof.
  elim: s => [ | x s' IHs] //; by rewrite !map_cons IHs.
Qed.
