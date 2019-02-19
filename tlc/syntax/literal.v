Require Import mathcomp.ssreflect.eqtype.
Require Import mathcomp.ssreflect.ssrbool.
Require Import mathcomp.ssreflect.ssreflect.
Require Import mathcomp.ssreflect.ssrnat.
Require Import tlc.operation.orientation.
Require Import tlc.operation.periodic_event.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Literal (non-inductive) terms *)
Inductive literal :=
| LUnit (u : unit)
| LBoolean (b : bool)
| LNatural (n : nat)
| LOrientation (o : orientation)
| LPeriodic (p : periodic_event).

(* Equality *)
Section eq.

  (* Boolean equality *)
  Definition literal_eq ll lr :=
    match ll, lr with
    | LUnit ul, LUnit ur => ul == ur
    | LUnit _, _ => false
    | LBoolean bl, LBoolean br => bl == br
    | LBoolean _, _ => false
    | LNatural nl, LNatural nr => nl == nr
    | LNatural _, _ => false
    | LOrientation ol, LOrientation or => ol == or
    | LOrientation _, _ => false
    | LPeriodic pl, LPeriodic pr => pl == pr
    | LPeriodic _, _ => false
    end.

  (* Boolean equality reflection *)
  Lemma literal_eqP : Equality.axiom literal_eq.
  Proof.
    case=> [ul | bl | nl | ol | pl]; case=> [ur | br | nr | or | pr] //=;
      try by constructor.
    - case H: (ul == ur); move/eqP: H => H //=; subst;
        last by constructor; move=> [].
      by constructor.
    - case H: (bl == br); move/eqP: H => H //=; subst;
        last by constructor; move=> [].
      by constructor.
    - case H: (nl == nr); move/eqP: H => H //=; subst;
        last by constructor; move=> [].
      by constructor.
    - case H: (ol == or); move/eqP: H => H //=; subst;
        last by constructor; move=> [].
      by constructor.
    - case H: (pl == pr); move/eqP: H => H //=; subst;
        last by constructor; move=> [].
      by constructor.
  Qed.

  (* EqType canonical structures *)
  Canonical Structure literal_eqMixin :=
    Eval hnf in EqMixin literal_eqP.
  Canonical Structure literal_eqType :=
    Eval hnf in EqType literal literal_eqMixin.

End eq.

(* Constructor coercions *)
Coercion LUnit : unit >-> literal.
Coercion LBoolean : bool >-> literal.
Coercion LNatural : nat >-> literal.
Coercion LOrientation : orientation >-> literal.
Coercion LPeriodic : periodic_event >-> literal.
