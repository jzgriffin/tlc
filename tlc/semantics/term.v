(* TLC in Coq
 *
 * Module: tlc.semantics.term
 * Purpose: Contains the semantics for term forms.
 *)

Require Import mathcomp.ssreflect.eqtype.
Require Import mathcomp.ssreflect.seq.
Require Import mathcomp.ssreflect.ssrbool.
Require Import mathcomp.ssreflect.ssreflect.
Require Import mathcomp.ssreflect.ssrnat.
Require Import tlc.semantics.constructor.
Require Import tlc.semantics.error.
Require Import tlc.semantics.pattern.
Require Import tlc.syntax.all_syntax.
Require Import tlc.utility.monad.
Require Import tlc.utility.result.
Require Import tlc.utility.seq.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Determine whether a term is a value
 * Values are constructors that are fully applied with value arguments.
 *)
Fixpoint is_value_rec t :=
  match t with
  | TParameter _ => None
  | TVariable _ => None
  | TConstructor c => Some (constructor_arity c)
  | TFunction _ => None
  | TUnknown _ => None
  | TApplication f a =>
    kf <- is_value_rec f;
    ka <- is_value_rec a;
    match kf, ka with
    | kf'.+1, 0 => Some kf'
    | _, _ => None
    end
  | TMatch _ => None
  end.
Definition is_value t := is_value_rec t == Some 0.

(* Derive the constructor and arguments of a value term
 * Returns Some (c, [x1, .., xn]) if the term t is of the form
 * (TConstructor c) ' x1 ' .. ' xn.
 *)
Fixpoint term_construction t :=
  match t with
  | TParameter _ => None
  | TVariable _ => None
  | TConstructor c => Some (c, [::])
  | TFunction _ => None
  | TUnknown _ => None
  | TApplication f x =>
    match term_construction f with
    | Some (c, xs) => Some (c, rcons xs x)
    | None => None
    end
  | TMatch _ => None
  end.

(* Every value term has a constructor *)
Lemma value_construction t :
  is_value t ->
  term_construction t <> None.
Proof.
Admitted.

(* Open a term t at depth k with bindings us *)
Fixpoint open_term_at k us t :=
  match t with
  | TParameter (P i j) =>
    if i == k then
      if onth us j is Some u then pure u
      else Failure (k, P i j)
    else pure t
  | TVariable _ => pure t
  | TConstructor _ => pure t
  | TFunction _ => pure t
  | TUnknown _ => pure t
  | TApplication f a =>
    f <- open_term_at k us f;
    a <- open_term_at k us a;
    pure (TApplication f a)
  | TMatch cs =>
    TMatch <$>
      (flatten_results ((fun '(p, b) =>
        match open_term_at k.+1 us b with
        | Success b => Success (p, b)
        | Failure e => Failure e
        end) <$> cs))
  end.
Definition open_term := open_term_at 0.

(* Determine whether a term is locally closed
 * A term is locally closed if every parameter reference is well-formed.
 *)
Fixpoint term_lc_in ks t :=
  match t with
  | TParameter (P i j) => if onth ks i is Some k then j < k else false
  | TVariable _ => true
  | TConstructor _ => true
  | TFunction _ => true
  | TUnknown _ => true
  | TApplication f a =>
    term_lc_in ks f && term_lc_in ks a
  | TMatch cs =>
    all (fun '(p, b) => term_lc_in (pattern_arity p :: ks) b) cs
  end.
Definition term_lc := term_lc_in [::].

(* Any term that is closed at depth ks is closed at depth k :: ks *)
Lemma term_lc_in_cons k ks t :
  term_lc_in ks t ->
  term_lc_in (k :: ks) t.
Proof.
Admitted.

(* Any term that is closed at depth ks is closed at depth ks' ++ ks *)
Lemma term_lc_in_concat ks' ks t :
  term_lc_in ks t ->
  term_lc_in (ks' ++ ks) t.
Proof.
  elim: ks' => [| k ks' IH] //=.
  by move=> H; specialize (IH H); apply term_lc_in_cons.
Qed.

(* Opening a closed term at a depth above its closure depth has no effect *)
Lemma open_lc_term_at k ks us t :
  k >= size ks ->
  term_lc_in ks t ->
  open_term_at k us t = Success t.
Proof.
Admitted.

(* Compute the set of flexible variables appearing in a term *)
Fixpoint term_flexibles t :=
  match t with
  | TParameter _ => [::]
  | TVariable (VF x) => [:: x]
  | TVariable (VR _) => [::]
  | TConstructor _ => [::]
  | TFunction _ => [::]
  | TUnknown _ => [::]
  | TApplication f a => term_flexibles f ++ term_flexibles a
  | TMatch cs => foldr cat [::] ((fun '(_, b) => term_flexibles b) <$> cs)
  end.

(* Compute the set of rigid variables appearing in a term *)
Fixpoint term_rigids t :=
  match t with
  | TParameter _ => [::]
  | TVariable (VF _) => [::]
  | TVariable (VR x) => [:: x]
  | TConstructor _ => [::]
  | TFunction _ => [::]
  | TUnknown _ => [::]
  | TApplication f a => term_rigids f ++ term_rigids a
  | TMatch cs => foldr cat [::] ((fun '(_, b) => term_rigids b) <$> cs)
  end.

(* Compute the set of variables appearing in a term *)
Definition term_vars t :=
  map VF (term_flexibles t) ++ map VR (term_rigids t).

(* Determine whether a term is globally closed
 * A term is globally closed if it contains no rigid variables.
 *)
Definition term_gc_in xs t := subset (term_rigids t) xs.
Definition term_gc := term_gc_in [::].

(* Determine whether a term is closed
 * A term is closed if it is locally and globally closed.
 *)
Definition term_closed_in ks xs t := term_lc_in ks t && term_gc_in xs t.
Definition term_closed t := term_lc t && term_gc t.

(* A closed term is locally closed *)
Lemma closed_term_lc ks xs t :
  term_closed_in ks xs t ->
  term_lc_in ks t.
Proof.
  by move/andP => [??].
Qed.

(* A closed term is globally closed *)
Lemma closed_term_gc ks xs t :
  term_closed_in ks xs t ->
  term_gc_in xs t.
Proof.
  by move/andP => [??].
Qed.

(* Determine whether a term is rigid
 * A term is rigid if it contains no flexible variables.
 *)
Fixpoint term_rigid t :=
  match t with
  | TParameter _ => true
  | TVariable (VR _) => true
  | TVariable (VF _) => false
  | TConstructor _ => true
  | TFunction _ => true
  | TUnknown _ => true
  | TApplication f a => term_rigid f && term_rigid a
  | TMatch cs => all (fun '(p, b) => term_rigid b) cs
  end.

(* Replace all instances of variable x with term u within t *)
Fixpoint replace_term_var x u t :=
  match t with
  | TParameter _ => t
  | TVariable y => if x == y then u else t
  | TConstructor _ => t
  | TFunction _ => t
  | TUnknown _ => t
  | TApplication f a =>
    TApplication (replace_term_var x u f) (replace_term_var x u a)
  | TMatch cs =>
    TMatch ((fun '(p, b) => (p, replace_term_var x u b)) <$> cs)
  end.

(* Replacing a flexible variable inside of a rigid term has no effect *)
Lemma replace_rigid_term_flexible_var (x : flexible) u t :
  term_rigid t ->
  replace_term_var x u t = t.
Proof.
Admitted.

(* Replacing a rigid variable inside of a globally-closed term has no effect *)
Lemma replace_gc_term_rigid_var (x : rigid) u t :
  term_gc t ->
  replace_term_var x u t = t.
Proof.
Admitted.

(* Determine whether a replacement within a term is compatible *)
Definition term_replace_compatible x u :=
  match x with
  | VR x => term_rigid u
  | VF x => true
  end.

(* Determine whether a replacement within a term is admissible *)
Definition term_replace_admissible x u :=
  term_replace_compatible x u && term_lc u.

(* Determine whether a term is known
 * A term is local if it does not contain any unknowns.
 *)
Fixpoint term_known t :=
  match t with
  | TParameter _ => true
  | TVariable _ => true
  | TConstructor _ => true
  | TFunction _ => true
  | TUnknown _ => false
  | TApplication f a => term_known f && term_known a
  | TMatch cs => all (fun '(p, b) => term_known b) cs
  end.

(* Determine whether all patterns in a term are well-formed *)
Fixpoint patterns_wf t :=
  match t with
  | TParameter _ => true
  | TVariable _ => true
  | TConstructor _ => true
  | TFunction _ => true
  | TUnknown _ => true
  | TApplication f a => patterns_wf f && patterns_wf a
  | TMatch cs => all (fun '(p, b) => pattern_wf p && patterns_wf b) cs
  end.

(* Determine whether a term is computable
 * This is a weaker form of type checking.  It checks whether a term is locally
 * and globally closed, rigid, known, and contains only well-formed patterns.
 *)
Definition term_computable t :=
  [&& term_closed t
    , term_rigid t
    , term_known t
    & patterns_wf t
    ].

(* A computable term is closed *)
Lemma computable_term_closed t :
  term_computable t ->
  term_closed t.
Proof.
  by move/andP => [??].
Qed.

(* A computable term is rigid *)
Lemma computable_term_rigid t :
  term_computable t ->
  term_rigid t.
Proof.
  by move/andP => [_]; move/andP => [? _].
Qed.

(* Reduce the application of an argument to a match.
 * If no match can be made between the patterns and the argument, EMatch will
 * be returned with an explanation for each matching failure.  If a match is
 * found, the case body will be opened using the bindings produced by the match.
 * If an error is encountered during opening, EOpenTerm will be returned to
 * explain what bindings were produced and which parameter was out of bounds.
 *)
Fixpoint reduce_match cs a :=
  match cs with
  | [::] => Failure (EEmptyMatch a)
  | (p, b) :: cs =>
    match match_pattern p a with
    | Success us =>
      match open_term us b with
      | Success t => Success t
      | Failure (k, x) => Failure (EOpenTerm b us k x)
      end
    | Failure pe =>
      match reduce_match cs a with
      | Success t => Success t
      | Failure e => Failure (EMatch p pe a e)
      end
    end
  end.

(* Reduce a term as far as possible given some amount of recursion fuel
 * This algorithm uses the fuel pattern to prove termination.
 *)
Fixpoint reduce_term_rec fuel t :=
  if fuel is fuel.+1 then
  match t with
  | TParameter _ => pure t
  | TVariable _ => pure t
  | TConstructor _ => pure t
  | TFunction _ => pure t
  | TUnknown _ => pure t
  | TApplication f a =>
    f' <- reduce_term_rec fuel f;
    a' <- reduce_term_rec fuel a;
    let t' := TApplication f' a' in
    match t' with
    | TApplication (TMatch cs) _ =>
      b <- reduce_match cs a';
      reduce_term_rec fuel b
    (* Boolean equality *)
    | TApplication (TApplication FEqual x1) x2 =>
      (* Only reduce this if the equality can be determined
       * Equality can be determined if the terms are syntactically equal or if
       * both terms are values.
       *)
      if x1 == x2 then pure TTrue
      else if is_value x1 && is_value x2 then pure TFalse
      else pure t'
    (* Naturals *)
    | TApplication (TApplication FAdd x1) x2 =>
      match nat_of_term x1, nat_of_term x2 with
      | Some x1', Some x2' => pure (term_of_nat (x1' + x2'))
      | Some x1', None => pure {-t term_of_nat x1' + x2 -}
      | None, Some x2' => pure {-t x1 + term_of_nat x2' -}
      | None, None => pure t
      end
    (* Lists *)
    | TApplication (TApplication FMap f) xs =>
      match xs with
      | CNil => pure xs
      | TApplication (TApplication CCons x) xs' =>
        reduce_term_rec fuel {-t (f ' x) :: (FMap ' f ' xs') -}
      | _ => pure t
      end
    | TApplication (TApplication FCount y) xs =>
      match xs with
      | CNil => pure TZero
      | TApplication (TApplication CCons x) xs' =>
        reduce_term_rec fuel {-t
          if: x == y then: CSucc ' (FCount ' y ' xs')
          else: FCount ' y ' xs'
        -}
      | _ => pure t'
      end
    | TApplication (TApplication FConcat xs1) xs2 =>
      match xs1 with
      | CNil => pure xs2
      | TApplication (TApplication CCons x) xs1 =>
        reduce_term_rec fuel {-t
          x :: (xs1 ++ xs2)
        -}
      | _ => pure t'
      end
    | TApplication (TApplication FSetUnion xs) ys =>
      match xs with
      | CNil => pure ys
      | TApplication (TApplication CCons x) xs' =>
        reduce_term_rec fuel {-t
          if: x \in ys then: xs' :|: ys
          else: x :: (xs' :|: ys)
        -}
      | _ => pure t'
      end
    | _ => pure t'
    end
  | TMatch _ => pure t
  end
  else Failure (EFuel t).

(* Reduce a term with a default amount of recursion fuel *)
Definition reduce_term_fuel := 4999.
Definition reduce_term := reduce_term_rec reduce_term_fuel.
Notation "[[t t ]]" := (reduce_term t) (at level 0, no associativity).
