Require Import Coq.Strings.Ascii.
Require Import mathcomp.ssreflect.eqtype.
Require Import mathcomp.ssreflect.seq.
Require Import mathcomp.ssreflect.ssrbool.
Require Import mathcomp.ssreflect.ssreflect.
Require Import mathcomp.ssreflect.ssrnat.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Export Coq.Strings.Ascii.

(* Equality *)
Section eq.

  (* Boolean equality *)
  Definition ascii_eq al ar :=
    match al, ar with
    | Ascii b0l b1l b2l b3l b4l b5l b6l b7l,
      Ascii b0r b1r b2r b3r b4r b5r b6r b7r =>
      [&& b0l == b0r, b1l == b1r, b2l == b2r, b3l == b3r,
          b4l == b4r, b5l == b5r, b6l == b6r & b7l == b7r]
    end.

  (* Boolean equality reflection *)
  Lemma ascii_eqP : Equality.axiom ascii_eq.
  Proof.
    case=> [b0l b1l b2l b3l b4l b5l b6l b7l]
      [b0r b1r b2r b3r b4r b5r b6r b7r] //=.
    case H: (b0l == b0r); move/eqP: H => H /=; subst;
      last by constructor; move=> [] => *; apply H.
    case H: (b1l == b1r); move/eqP: H => H /=; subst;
      last by constructor; move=> [] => *; apply H.
    case H: (b2l == b2r); move/eqP: H => H /=; subst;
      last by constructor; move=> [] => *; apply H.
    case H: (b3l == b3r); move/eqP: H => H /=; subst;
      last by constructor; move=> [] => *; apply H.
    case H: (b4l == b4r); move/eqP: H => H /=; subst;
      last by constructor; move=> [] => *; apply H.
    case H: (b5l == b5r); move/eqP: H => H /=; subst;
      last by constructor; move=> [] => *; apply H.
    case H: (b6l == b6r); move/eqP: H => H /=; subst;
      last by constructor; move=> [] => *; apply H.
    case H: (b7l == b7r); move/eqP: H => H /=; subst;
      last by constructor; move=> [] => *; apply H.
    by constructor.
  Qed.

  (* EqType canonical structures *)
  Canonical Structure ascii_eqMixin := EqMixin ascii_eqP.
  Canonical Structure ascii_eqType :=
    Eval hnf in EqType ascii ascii_eqMixin.

End eq.
