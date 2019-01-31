Require Import Coq.Strings.String.
Require Import mathcomp.ssreflect.eqtype.
Require Import mathcomp.ssreflect.ssrbool.
Require Import mathcomp.ssreflect.ssreflect.
Require Import tlc.utility.ascii.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Export Coq.Strings.String.

(* Equality *)
Section eq.

  (* Boolean equality *)
  Fixpoint string_eq sl sr :=
    match sl, sr with
    | EmptyString, EmptyString => true
    | String al sl', String ar sr' => (al == ar) && string_eq sl' sr'
    | _, _ => false
    end.

  (* Boolean equality reflection *)
  Lemma string_eqP : Equality.axiom string_eq.
  Proof.
    elim=> [ | al sl' IHsl'] [ | ar sr'] /=; try by constructor.
    apply/(iffP idP).
    - by move/andP=> [Ha Hs']; move/eqP: Ha <-; move/IHsl': Hs' <-.
    - move=> [] => Ha Hs'; subst; apply/andP; split;
      [exact: eq_refl | by apply/(IHsl' sr')].
  Qed.

  (* EqType canonical structures *)
  Canonical Structure string_eqMixin := EqMixin string_eqP.
  Canonical Structure string_eqType :=
    Eval hnf in EqType string string_eqMixin.

End eq.
