Require Import TLC.Utility.Fin.
Require Import Coq.Lists.List.
Require Import Coq.Vectors.Fin.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Heterogeneous lists
 * Credit: Adam Chlipala, http://adam.chlipala.net/cpdt/html/DataStruct.html
 *)
Section hlist.

  Variable T : Type.
  Variable M : T -> Type.

  Inductive hlist : list T -> Type :=
  | HLNil : hlist nil
  | HLCons (x : T) (xs : list T) : M x -> hlist xs -> hlist (x :: xs).

  Variable x' : T.

  Inductive hmember : list T -> Type :=
  | HMFirst xs : hmember (x' :: xs)
  | HMNext x xs : hmember xs -> hmember (x :: xs).

  Fixpoint hget xs (mxs : hlist xs) : hmember xs -> M x' :=
    match mxs with
    | HLNil => fun m =>
      match m in hmember xs'
      return (match xs' with
        | nil => M x'
        | _ :: _ => unit
      end)
      with
      | HMFirst _ => tt
      | HMNext _ _ => tt
      end
    | HLCons x mxs' => fun m =>
      match m in hmember xs'
      return (match xs' with
        | nil => Empty_set
        | x'' :: xs'' => M x'' -> (hmember xs'' -> M x') -> M x'
      end)
      with
      | HMFirst _ => fun x _ => x
      | HMNext _ m' => fun _ get_mxs' => get_mxs' m'
      end x (hget mxs')
    end.

  Fixpoint hoffset xs : hmember xs -> nat.
  Proof.
    destruct xs; intros m; [inversion m | ].
    destruct m; [exact 0 | exact (S (hoffset xs0 m))].
  Admitted. (* TODO *)

  Fixpoint hindex xs : hmember xs -> index xs.
  Proof.
    destruct xs; intros m; [inversion m | ].
    destruct m; [exact Fin.F1 | exact (Fin.FS (hindex xs0 m))].
  Admitted. (* TODO *)

End hlist.

(* Arguments for heterogeneous list constructors *)
Arguments HLNil [T M].
Arguments HLCons [T M x xs].

(* Arguments for heterogeneous member constructors *)
Arguments HMFirst [T x' xs].
Arguments HMNext [T x' x xs].

(* Notation scope for heterogeneous lists *)
Delimit Scope hlist_scope with hl.
Bind Scope hlist_scope with hlist.

(* Constructor notations for heterogeneous lists *)
Notation "[ ]" := HLNil : hlist_scope.
Notation "x :: y" := (HLCons x y) : hlist_scope.
Notation "[ x ]" := (x :: [])%hl : hlist_scope.
Notation "[ x ; y ; .. ; z ]" := (HLCons x (HLCons y (.. (HLCons z HLNil) ..)))
  : hlist_scope.

(* Notation scope for heterogeneous members *)
Delimit Scope hmember_scope with hm.
Bind Scope hmember_scope with hmember.

(* Constructor notations for heterogeneous members *)
Notation "0" := (HMFirst) (at level 0) : hmember_scope.
Notation "x +1" := (HMNext x) (at level 0) : hmember_scope.

(* Notations for the heterogeneous getter *)
Notation "x [@ y ]" := (hget x y) (at level 0) : core_scope.
