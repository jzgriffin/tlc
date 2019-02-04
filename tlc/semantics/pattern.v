Require Import mathcomp.ssreflect.seq.
Require Import mathcomp.ssreflect.ssreflect.
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
  (* Unit *)
  | {p: CUnit}, {t: CUnit} => pure [::]
  (* Product *)
  | {p: (pl, pr)}, {t: (tl, tr)} =>
    tsl <- match_pattern pl tl;
    tsr <- match_pattern pr tr;
    pure (app tsl tsr)
  (* Sum *)
  | {p: CLeft $ p}, {t: CLeft $ t} => match_pattern p t
  | {p: CRight $ p}, {t: CRight $ t} => match_pattern p t
  (* Boolean *)
  | {p: CTrue}, {t: CTrue} => pure [::]
  | {p: CFalse}, {t: CFalse} => pure [::]
  (* Natural *)
  | {p: 0}, {t: 0} => pure [::]
  | {p: p.+1}, {t: t.+1} => match_pattern p t
  (* List *)
  | {p: []}, {t: []} => pure [::]
  | {p: px :: pxs}, {t: tx :: txs} =>
    tsx <- match_pattern px tx;
    tsxs <- match_pattern pxs txs;
    pure (app tsx tsxs)
  (* Failure *)
  | _, _ => Failure (EMatch p t)
  end.
