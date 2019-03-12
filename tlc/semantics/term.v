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
Require Import tlc.semantics.environment.
Require Import tlc.semantics.equivalents.
Require Import tlc.semantics.error.
Require Import tlc.semantics.pattern.
Require Import tlc.syntax.all_syntax.
Require Import tlc.utility.monad.
Require Import tlc.utility.partial_map.
Require Import tlc.utility.result.
Require Import tlc.utility.seq.
Require Import tlc.utility.set.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Substitutes terms in term t with terms from equivalence map e *)
Reserved Notation "t /t/ e" (at level 40, left associativity).
Reserved Notation "c /c/ e" (at level 40, left associativity).
Reserved Notation "cs /cs/ e" (at level 40, left associativity).
Fixpoint substitute_term (e : equivalents) t :=
  if e{@t} is Some t' then t' else
  match t with
  | TFailure => t
  | TParameter _ => t
  | TVariable _ => t
  | TConstructor _ => t
  | TLiteral _ => t
  | TFunction _ => t
  | TApplication tf ta => TApplication (tf /t/ e) (ta /t/ e)
  | TAbstraction tb => TAbstraction (tb /t/ e)
  | TMatch ta cs => TMatch (ta /t/ e) (cs /cs/ e)
  end
with substitute_case (e : equivalents) c :=
  match c with
  | TCase p t => TCase p (t /t/ e)
  end
with substitute_cases (e : equivalents) cs :=
  match cs with
  | TCNil => TCNil
  | TCCons c cs => TCCons (c /c/ e) (cs /cs/ e)
  end
where "t /t/ e" := (substitute_term e t)
  and "c /c/ e" := (substitute_case e c)
  and "cs /cs/ e" := (substitute_cases e cs).

(* Substitutes free variables in a term t with terms from environment e
 * NOTE: This process is not capture-avoiding.
 *)
Definition instantiate_term (e : environment) t :=
  t /t/ environment_equivalents e.

(* Computes the set of free variables in a term *)
Fixpoint term_free t :=
  match t with
  | TFailure => [::]
  | TParameter _ => [::]
  | TVariable v => [:: v]
  | TConstructor _ => [::]
  | TLiteral _ => [::]
  | TFunction _ => [::]
  | TApplication tf ta => term_free tf \union term_free ta
  | TAbstraction tb => term_free tb
  | TMatch ta cs => term_free ta \union cases_free cs
  end
with case_free c :=
  match c with
  | TCase _ t => term_free t
  end
with cases_free cs :=
  match cs with
  | TCNil => [::]
  | TCCons c cs => case_free c \union cases_free cs
  end.

(* Determines whether a term is globally closed
 * A term is globally closed if it contains no free variables.
 *)
Definition is_term_closed t := nilp (term_free t).

(* Opens a term t at a particular depth k
 * Opening a term replaces all bound variables at depth k with terms from the
 * replacement term list us.
 *)
Reserved Notation "{ k :-> us } t" (at level 0, no associativity).
Fixpoint open_term_at k us t :=
  match t with
  | TFailure => pure t
  | TParameter (P i j) =>
    if i == k then
      nth (Failure (EParameter (P i j))) (map Success us) j
    else pure t
  | TVariable _ => pure t
  | TConstructor _ => pure t
  | TLiteral _ => pure t
  | TFunction _ => pure t
  | TApplication tf ta =>
    tf <- {k :-> us} tf;
    ta <- {k :-> us} ta;
    pure (TApplication tf ta)
  | TAbstraction tb =>
    tb <- {k.+1 :-> us} tb;
    pure (TAbstraction tb)
  | TMatch ta cs =>
    ta <- {k :-> us} ta;
    cs <- open_cases_at k.+1 us cs;
    pure (TMatch ta cs)
  end
with open_case_at k us c :=
  match c with
  | TCase p t =>
    t <- {k :-> us} t;
    pure (TCase p t)
  end
with open_cases_at k us c :=
  match c with
  | TCNil => pure c
  | TCCons c cs =>
    c <- open_case_at k us c;
    cs <- open_cases_at k us cs;
    pure (TCCons c cs)
  end
where "{ k :-> us } t" := (open_term_at k us t).

(* Opens a term at depth 0 *)
Definition open_term := open_term_at 0.
Notation "t ^ us" := (open_term us t).

(* Converts a cases to a list of case *)
Fixpoint lift_cases cs :=
  match cs with
  | TCNil => [::]
  | TCCons c cs => c :: lift_cases cs
  end.

(* Converts a unit literal term to a unit *)
Definition lift_unit (t : term) :=
  match t with
  | LUnit u => pure u
  | _ => Failure (EBoolean t)
  end.

(* Converts a Boolean literal term to a bool *)
Definition lift_boolean (t : term) :=
  match t with
  | LBoolean b => pure b
  | _ => Failure (EBoolean t)
  end.

(* Converts a natural literal term to a nat *)
Definition lift_natural (t : term) :=
  match t with
  | LNatural n => pure n
  | _ => Failure (ENatural t)
  end.

(* Converts an orientation literal term to an orientation *)
Definition lift_orientation (t : term) :=
  match t with
  | LOrientation o => pure o
  | _ => Failure (ENatural t)
  end.

(* Converts a periodic literal term to a periodic *)
Definition lift_periodic (t : term) :=
  match t with
  | LPeriodic p => pure p
  | _ => Failure (ENatural t)
  end.

(* Converts a list term to a seq *)
Fixpoint lift_list (ts : term) :=
  match ts with
  | CNil => pure [::]
  | {t: CCons $ t $ ts} => ts <- lift_list ts; pure (t :: ts)
  | _ => Failure (EList ts)
  end.

(* Evaluates a term as far as possible given some amount of recursion fuel
 * This algorithm uses the fuel pattern to prove termination.
 *
 * NOTE: Whenever an external function is added, it must be implemented here.
 *)
Fixpoint evaluate_term' fuel t :=
  if fuel is fuel.+1 then
    match t with
    | TFailure => Failure EFailure
    | TParameter p => Failure (EParameter p)
    | TVariable _ => pure t
    | TConstructor _ => pure t
    | TLiteral _ => pure t
    | TFunction _ => pure t
    | TApplication tf ta =>
      tf <- evaluate_term' fuel tf;
      ta <- evaluate_term' fuel ta;
      if tf is TAbstraction tf then
        t <- tf^[:: ta];
        evaluate_term' fuel t
      else
        let t := TApplication tf ta in
        if is_term_closed t then
          (* External function evaluation *)
          match t with
          (* Generic *)
          | {t: FEqual $ tl $ tr} =>
            pure (TLiteral (LBoolean (tl == tr)))
          (* Boolean *)
          | {t: FNot $ t} =>
            t <- lift_boolean t;
            pure (TLiteral (LBoolean (negb t)))
          | {t: FOr $ tl $ tr} =>
            tl <- lift_boolean tl;
            tr <- lift_boolean tr;
            pure (TLiteral (LBoolean (tl || tr)))
          (* Natural *)
          | {t: FSucc $ t} =>
            t <- lift_natural t;
            pure (TLiteral (LNatural (t.+1)))
          | {t: FAdd $ tl $ tr} =>
            tl <- lift_natural tl;
            tr <- lift_natural tr;
            pure (TLiteral (LNatural (tl + tr)))
          (* List *)
          | {t: FConcat $ tsl $ tsr} =>
            tsl <- lift_list tsl;
            tsr <- lift_list tsr;
            pure (TList (app tsl tsr))
          | {t: FCount $ t $ ts} =>
            ts <- lift_list ts;
            pure (TLiteral (LNatural (count_mem t ts)))
          | {t: FUnion $ tsl $ tsr} =>
            tsl <- lift_list tsl;
            tsr <- lift_list tsr;
            pure (TList (tsl \union tsr))
          | {t: FMap $ tf $ ts} =>
            ts <- lift_list ts;
            evaluate_term' fuel (TList [seq {t: tf $ t} | t <- ts])
          (* Default *)
          | _ => pure t
          end
        else pure t
    | TAbstraction _ => pure t
    | TMatch ta cs =>
      ta <- evaluate_term' fuel ta;
      let f c t :=
        if t is Success _ then t
        else
          match c with
          | TCase p tp =>
            if match_pattern p ta is Success us then
              tp <- tp^us;
              evaluate_term' fuel tp
            else t
          end
      in
      if foldr f (Failure (EMatch ta cs)) (lift_cases cs) is Success t then
        pure t
      else pure (TMatch ta cs)
    end
  else Failure (EFuel t).

(* Evaluates a term with a default amount of recursion fuel *)
Definition evaluate_term_fuel := 4999.
Definition evaluate_term := evaluate_term' evaluate_term_fuel.
Notation "[[t t ]]" := (evaluate_term t) (at level 0, no associativity).

(* Tactics for semantic operations on terms *)
Ltac substitute_term :=
  rewrite /substitute_term /=.
Ltac instantiate_term :=
  rewrite /instantiate_term /=.
Ltac evaluate_term :=
  rewrite /evaluate_term /=.
