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
 * bindings in p. Operates in the result monad *)
Fixpoint match_pattern (p : pattern) (t : term) :=
  match p, t with
  (* Generic *)
  | {p: %}, _ => pure [::]
  | {p: #}, _ => pure [:: t]
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
  (* Unit *)
  | PLUnit pu, LUnit tu =>
    if pu == tu then pure [::]
    else Failure (EMatch p t)
  (* Boolean *)
  | PLBoolean pb, LBoolean tb =>
    if pb == tb then pure [::]
    else Failure (EMatch p t)
  (* Natural *)
  | PLNatural pn, LNatural tn =>
    if pn == tn then pure [::]
    else Failure (EMatch p t)
  | {p: pn.+1}, {t: LNatural tn.+1} => match_pattern pn tn
  (* Orientation *)
  | PLOrientation po, LOrientation to =>
    if po == to then pure [::]
    else Failure (EMatch p t)
  (* Periodic *)
  | PLPeriodic pp, LPeriodic tp =>
    if pp == tp then pure [::]
    else Failure (EMatch p t)
  (* Failure *)
  | _, _ => Failure (EMatch p t)
  end.
