Require Import TLC.Syntax.Constant.
Require Import TLC.Syntax.Expression.
Require Import TLC.Syntax.Flexible.
Require Import TLC.Syntax.Formula.
Require Import Coq.Lists.List.
Require TLC.Syntax.Component.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module SC := TLC.Syntax.Component.

(* Basic syntactic rules and axioms *)
Section derives.

  Reserved Notation "x |- y" (at level 0).

  Inductive derives : list formula -> formula -> Prop :=
  (* Sequent logic *)
  | DSAxiom X f :
    (f :: X) |- f
  | DSThin X f1 f2 :
    X |- f2 ->
    (f1 :: X) |- f2
  | DSContraction X f1 f2 :
    (f1 :: f1 :: X) |- f2 ->
    (f1 :: X) |- f2
  | DSExchange X f1 f2 f3 :
    (f1 :: f2 :: X) |- f3 ->
    (f2 :: f1 :: X) |- f3
  | DSCut X f1 f2 :
    X |- f1 ->
    (f1 :: X) |- f2 ->
    X |- f2
  | DSNotL X f1 f2 :
    X |- f1 ->
    ((~f1)%f :: X) |- f2
  | DSNotR X f :
    (f :: X) |- FFalse ->
    X |- (~f)%f
  | DSOrL X f1 f2 f3 :
    (f1 :: X) |- f3 ->
    (f2 :: X) |- f3 ->
    ((f1 \/ f2)%f :: X) |- f3
  | DSOrRL X f1 f2 :
    X |- f1 ->
    X |- (f1 \/ f2)
  | DSOrRR X f1 f2 :
    X |- f2 ->
    X |- (f1 \/ f2)
  | DSAndL X f1 f2 f3 :
    (f1 :: f2 :: X) |- f3 ->
    ((f1 /\ f2)%f :: X) |- f3
  | DSAndR X f1 f2 :
    X |- f1 ->
    X |- f2 ->
    X |- (f1 /\ f2)
  | DSIfL X f1 f2 f3 :
    X |- f1 ->
    (f2 :: X) |- f3 ->
    ((f1 -> f2)%f :: X) |- f3
  | DSIfR X f1 f2 :
    (f1 :: X) |- f2 ->
    X |- (f1 -> f2)
  (* TODO: DForAllL *)
  (* TODO: DForAllR *)
  (* TODO: DExistsL *)
  (* TODO: DExistsR *)
  (* Temporal logic future axioms *)
  | DT1 X f :
    X |- (always f -> f)
  | DT2 X f :
    X |- ((next ~f) <=> ~next f)
  | DT3 X f1 f2 :
    X |- ((next (f1 -> f2)) <=> (next f1 -> next f2))
  | DT4 X f1 f2 :
    X |- ((always (f1 -> f2)) =>> (always f1 -> always f2))
  | DT5 X f :
    X |- ((always f) -> always next f)
  | DT6 X f :
    X |- ((f =>> next f) -> (f =>> always f))
  | DT7 X f1 f2 :
    X |- ((f1 unless f2) <=> (f2 \/ (f1 /\ next (f1 unless f2))))
  | DT8 X f1 f2 :
    X |- ((always f1) =>> f1 unless f2)
  (* Temporal logic past axioms *)
  | DT9 X f :
    X |- (previous f =>> previous^ f)
  | DT10 X f1 f2 :
    X |- (previous^ (f1 -> f2) <=> (previous^ f1 -> previous^ f2))
  | DT11 X f1 f2 :
    X |- (alwaysp (f1 -> f2) =>> (alwaysp f1 -> alwaysp f2))
  | DT12 X f :
    X |- (always f -> always previous^ f)
  | DT13 X f :
    X |- ((f =>> previous^ f) -> (f =>> alwaysp f))
  | DT14 X f1 f2 :
    X |- ((f1 backto f2) <=> (f2 \/ (f1 /\ previous^ (f1 backto f2))))
  | DT15 X :
    X |- previous^ FFalse
  (* Temporal logic mixed axioms *)
  | DT16 X f :
    X |- (f =>> next previous f)
  | DT17 X f :
    X |- (f =>> previous^ next f)
  (* Temporal logic rules *)
  | DTGeneralization X f :
    X |- f ->
    X |- always f
  (* TODO: Axiom18 *)
  (* Program logic *)
  | DPNode X :
    X |- always (Fn \in CNodes)
  | DPIR {P} (C : SC.component P) X e :
    X |- (when[]-> e =>>
      (Fs' <- Fn, Fors, Fois) = (SC.request C) <- Fn <- (Fs <- Fn) <- e)
  where "x |- y" := (derives x y).

End derives.

Notation "x |- y" := (derives x y) (at level 0).

(* Derived rules and lemmas *)
Section derived.

  Lemma Lemma84 X f : X |- (eventually f <=> eventually eventually f).
  Proof.
  Admitted. (* TODO *)

End derived.

(* Rewriting within a proof *)
Section rewriting.

  Fixpoint rewrite_congruent X f1 f2 (H : X |- (f1 <=> f2)) f :=
    if formula_eqb f1 f then f2 else
    match f with
    | FFalse => FFalse
    | FNot f' => FNot (rewrite_congruent H f')
    | FOr f1' f2' => FOr (rewrite_congruent H f1') (rewrite_congruent H f2')
    | FPredicate p => FPredicate p
    | FForAll f' => FForAll (rewrite_congruent H f')
    | FUntil' f1' f2' =>
      FUntil' (rewrite_congruent H f1') (rewrite_congruent H f2')
    | FSince' f1' f2' =>
      FSince' (rewrite_congruent H f1') (rewrite_congruent H f2')
    end.

  Lemma rewrite_congruent_correct X f1 f2 (H : X |- (f1 <=> f2)) f :
    X |- (rewrite_congruent H f) <-> X |- f.
  Proof.
  Admitted. (* TODO *)

End rewriting.

Ltac clean_expression :=
  repeat rewrite expression_eqb_refl;
  simpl.

Ltac rewrite_congruent H :=
  apply (rewrite_congruent_correct H).
