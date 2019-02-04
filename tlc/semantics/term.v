Require Import mathcomp.ssreflect.eqtype.
Require Import mathcomp.ssreflect.seq.
Require Import mathcomp.ssreflect.ssrbool.
Require Import mathcomp.ssreflect.ssreflect.
Require Import mathcomp.ssreflect.ssrnat.
Require Import tlc.semantics.environment.
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

(* Substitutes free variables in term t with terms from environment E *)
Reserved Notation "t [t/ E ]" (at level 1, left associativity).
Fixpoint substitute_term (E : environment) t :=
  match t with
  | TFailure => t
  | TParameter _ => t
  | TVariable v => if E{@v} is Some t' then t' else t
  | TConstructor _ => t
  | TFunction _ => t
  | TApplication tf ta => TApplication tf[t/E] ta[t/E]
  | TAbstraction tb => TAbstraction tb[t/E]
  | TMatch p ta tm tf => TMatch p ta[t/E] tm[t/E] tf[t/E]
  end
where "t [t/ E ]" := (substitute_term E t).

(* Computes the set of free variables in a term *)
Fixpoint term_free t :=
  match t with
  | TFailure => [::]
  | TParameter _ => [::]
  | TVariable v => [:: v]
  | TConstructor _ => [::]
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

(* Converts a Boolean term to a bool *)
Definition lift_boolean (t : term) :=
  match t with
  | {t: CTrue} => pure true
  | {t: CFalse} => pure false
  | _ => Failure (EBoolean t)
  end.

(* Converts a natural term to a nat *)
Fixpoint lift_natural (t : term) :=
  match t with
  | {t: CZero} => pure 0
  | {t: CSucc $ x} => n <- lift_natural x; pure n.+1
  | _ => Failure (ENatural t)
  end.

(* Converts a list term to a seq *)
Fixpoint lift_list (ts : term) :=
  match ts with
  | {t: []} => pure [::]
  | {t: t :: ts} => ts <- lift_list ts; pure (t :: ts)
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
          | {t: tl = tr} => pure (TBoolean (tl == tr))
          (* Boolean *)
          | {t: ~t} =>
            t <- lift_boolean t;
            pure (TBoolean (negb t))
          | {t: tl \/ tr} =>
            tl <- lift_boolean tl;
            tr <- lift_boolean tr;
            pure (TBoolean (tl || tr))
          (* Natural *)
          | {t: tl + tr} =>
            tl <- lift_natural tl;
            tr <- lift_natural tr;
            pure (TNatural (tl + tr))
          (* List *)
          | {t: FCount $ t $ ts} =>
            ts <- lift_list ts;
            pure (TNatural (count_mem t ts))
          | {t: tsl \union tsr} =>
            tsl <- lift_list tsl;
            tsr <- lift_list tsr;
            pure (TList (tsl \union tsr))
          | {t: tf <$> ts} =>
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
Notation "[[ t ]]" := (evaluate_term t) (at level 0, no associativity).

(* Tactic for evaluation *)
Ltac evaluate_term := rewrite /evaluate_term /=.
