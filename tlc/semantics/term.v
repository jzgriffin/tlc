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
  | TMatch p ta tm tf => TMatch p (ta /t/ e) (tm /t/ e) (tf /t/ e)
  end
where "t /t/ e" := (substitute_term e t).

(* Substitutes free variables in a term t with terms from environment e *)
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
  | TMatch _ ta tm tf => term_free ta \union term_free tm \union term_free tf
  end.

(* Determines whether a term is globally closed
 * A term is globally closed if it contains no free variables *)
Definition is_term_closed t := nilp (term_free t).

(* Opens a term t at a particular depth k, replacing all bound variables at
 * that depth with terms from the replacement terms us
 * See "The Locally Nameless Representation" by Arthur Chargueraud
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
  | TMatch p ta tm tf =>
    ta <- {k :-> us} ta;
    tm <- {k.+1 :-> us} tm;
    tf <- {k.+1 :-> us} tf;
    pure (TMatch p ta tm tf)
  end
where "{ k :-> us } t" := (open_term_at k us t).

(* Opens a term at depth 0 *)
Definition open_term := open_term_at 0.
Notation "t ^ us" := (open_term us t).

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

(* Evaluates a term as far as possible given some amount of recursion fuel *)
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
    | TMatch p ta tm tf =>
      ta <- evaluate_term' fuel ta;
      if match_pattern p ta is Success us then
        t <- tm^us;
        evaluate_term' fuel t
      else evaluate_term' fuel tf
    end
  else Failure (EFuel t).

(* Evaluates a term with a default amount of recursion fuel *)
Definition evaluate_term_fuel := 4999.
Definition evaluate_term := evaluate_term' evaluate_term_fuel.
Notation "[[t t ]]" := (evaluate_term t) (at level 0, no associativity).

(* Tactic for evaluation *)
Ltac evaluate_term := rewrite /evaluate_term /=.
