(* TLC in Coq
 *
 * Module: tlc.semantics.pattern
 * Purpose: Contains the pattern matching algorithm.
 *)

Require Import Coq.Arith.PeanoNat.
Require Import Coq.Numbers.DecimalString.
Require Import mathcomp.ssreflect.eqtype.
Require Import mathcomp.ssreflect.seq.
Require Import mathcomp.ssreflect.ssrbool.
Require Import mathcomp.ssreflect.ssreflect.
Require Import mathcomp.ssreflect.ssrnat.
Require Import tlc.operation.orientation.
Require Import tlc.operation.periodic_event.
Require Import tlc.semantics.error.
Require Import tlc.syntax.all_syntax.
Require Import tlc.utility.monad.
Require Import tlc.utility.result.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Pattern matching algorithm
 * Matches a term t against a pattern p and returns the list of terms bound by
 * bindings in p.  Operates in the result monad.
 *
 * NOTE: Whenever a new data constructor or literal constructor is added, it
 * must be added to the algorithm in order to be used for pattern matching.
 *)
Fixpoint match_pattern (p : pattern) (t : term) :=
  match p, t with
  (* Generic *)
  | {p: %}, _ => pure [::] (* Matches anything, binds nothing *)
  | {p: #}, _ => pure [:: t] (* Matches and binds anything *)
  (* Product *)
  | {p: CPair $ pl $ pr}, {t: CPair $ tl $ tr} =>
    tsl <- match_pattern pl tl;
    tsr <- match_pattern pr tr;
    pure (app tsl tsr)
  (* Sum *)
  | {p: CLeft $ p}, {t: CLeft $ t} => match_pattern p t
  | {p: CRight $ p}, {t: CRight $ t} => match_pattern p t
  (* List *)
  | {p: CNil}, {t: CNil} => pure [::]
  | {p: CCons $ px $ pxs}, {t: CCons $ tx $ txs} =>
    tsx <- match_pattern px tx;
    tsxs <- match_pattern pxs txs;
    pure (app tsx tsxs)
  (* FLRequest *)
  | {p: CFLSend $ pn $ pm}, {t: CFLSend $ tn $ tm} =>
    tsn <- match_pattern pn tn;
    tsm <- match_pattern pm tm;
    pure (app tsn tsm)
  (* FLIndication *)
  | {p: CFLDeliver $ pn $ pm}, {t: CFLDeliver $ tn $ tm} =>
    tsn <- match_pattern pn tn;
    tsm <- match_pattern pm tm;
    pure (app tsn tsm)
  (* SLRequest *)
  | {p: CSLSend $ pn $ pm}, {t: CSLSend $ tn $ tm} =>
    tsn <- match_pattern pn tn;
    tsm <- match_pattern pm tm;
    pure (app tsn tsm)
  (* SLIndication *)
  | {p: CSLDeliver $ pn $ pm}, {t: CSLDeliver $ tn $ tm} =>
    tsn <- match_pattern pn tn;
    tsm <- match_pattern pm tm;
    pure (app tsn tsm)
  (* PLRequest *)
  | {p: CPLSend $ pn $ pm}, {t: CPLSend $ tn $ tm} =>
    tsn <- match_pattern pn tn;
    tsm <- match_pattern pm tm;
    pure (app tsn tsm)
  (* PLIndication *)
  | {p: CPLDeliver $ pn $ pm}, {t: CPLDeliver $ tn $ tm} =>
    tsn <- match_pattern pn tn;
    tsm <- match_pattern pm tm;
    pure (app tsn tsm)
  (* Unit *)
  | PLUnit pu, LUnit tu =>
    if pu == tu then pure [::]
    else Failure (EPattern p t)
  (* Boolean *)
  | PLBoolean pb, LBoolean tb =>
    if pb == tb then pure [::]
    else Failure (EPattern p t)
  (* Natural *)
  | PLNatural pn, LNatural tn =>
    if pn == tn then pure [::]
    else Failure (EPattern p t)
  | {p: pn.+1}, {t: LNatural tn.+1} => match_pattern pn tn
  (* Orientation *)
  | PLOrientation po, LOrientation to =>
    if po == to then pure [::]
    else Failure (EPattern p t)
  (* Periodic *)
  | PLPeriodic pp, LPeriodic tp =>
    if pp == tp then pure [::]
    else Failure (EPattern p t)
  (* Failure *)
  | _, _ => Failure (EPattern p t)
  end.

(* Constructs a term equivalent to a pattern p
 * Produces a tuple of term, number of free variables, and free variable names
 * n is the current number of free variables
 * vs is the current set of free variable names
 *
 * Example:
 *   pattern_term {p: (#, %, %)} 0 [::] =
 *     ({t: ("?0", "?1", "?2")}, 3, [:: "?2", "?1", "?0"]
 *)
Fixpoint pattern_term p n vs :=
  match p with
  | PWildcard
  | PBinding =>
    let v := V ("?" ++ (NilZero.string_of_uint (Nat.to_uint n))) in
    (TVariable v, S n, v :: vs)
  | PConstructor c => (TConstructor c, n, vs)
  | PApplication pf pa =>
    let '(tf, nf, vsf) := pattern_term pf n vs in
    let '(ta, na, vsa) := pattern_term pa nf vsf in
    ({t: tf $ ta}, na, vsa)
  (* Literals *)
  | PLUnit u => (TLiteral (LUnit u), n, vs)
  | PLBoolean b => (TLiteral (LBoolean b), n, vs)
  | PLNatural n => (TLiteral (LNatural n), n, vs)
  | PLSucc p =>
    let '(t, n, vs) := pattern_term p n vs in
    ({t: t.+1}, n, vs)
  | PLOrientation o => (TLiteral (LOrientation o), n, vs)
  | PLPeriodic p => (TLiteral (LPeriodic p), n, vs)
  end.

(* Destructs a case into an assertion about that case
 * ta is the term being destructed
 * c is the case to destruct on
 * Ac is the goal assertion
 * f is a function that produces the form of the destructed assertion
 * The resulting assertion is universally quantified on all free variables
 * generated.
 *)
Definition destruct_case ta c Ac
  (f : term -> term -> assertion -> assertion) :=
  match c with
  | TCase p t =>
    let '(pt, _, vs) := pattern_term p 0 [::] in
    foldr (fun v A => AForAll v A) (f ta pt Ac) vs
  end.

(* Destructs a case into an assertion for use in the premise *)
Definition destruct_casep ta c Ac :=
  destruct_case ta c Ac (fun ta pt Ac => {A: ta = pt /\ Ac}).

(* Destructs a case into an assertion for use in the conclusion *)
Definition destruct_casec ta c Ac :=
  destruct_case ta c Ac (fun ta pt Ac => {A: ta = pt -> Ac}).

(* Destructs a match into an assertion about the possible cases of that
 * assertion
 *)
Fixpoint destruct_match P ta cs
  (dc : term -> case -> assertion -> assertion) :=
  match cs with
  | TCNil => ATrue
  | TCCons c TCNil =>
    {A: dc ta c (P (TMatch ta cs))}
  | TCCons c cs' =>
    {A: (dc ta c (P (TMatch ta cs))) \/ destruct_match P ta cs' dc}
  end.

(* Destructs a match into an assertion for use in the premise *)
Definition destruct_matchp P ta cs := destruct_match P ta cs destruct_casep.

(* Destructs a match into an assertion for use in the conclusion *)
Definition destruct_matchc P ta cs := destruct_match P ta cs destruct_casec.
