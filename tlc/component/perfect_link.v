(* TLC in Coq
 *
 * Module: tlc.component.perfect_link
 * Purpose: Contains the functional implementation of the perfect link component.
 *)

Require Import mathcomp.ssreflect.eqtype.
Require Import mathcomp.ssreflect.seq.
Require Import mathcomp.ssreflect.ssrbool.
Require Import mathcomp.ssreflect.ssreflect.
Require Import mathcomp.ssreflect.ssrnat.
Require Import tlc.component.component.
Require Import tlc.component.stubborn_link_spec.
Require Import tlc.logic.all_logic.
Require Import tlc.semantics.all_semantics.
Require Import tlc.syntax.all_syntax.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Functional implementation *)
Definition perfect_link :=
  let slc := 0 in
  let initialize :=
    {-t fun: (* n *)
      (0, [])
     -} in
  let request :=
    {-t fun: fun: fun: (* n, s, ir *)
      let: ($0, $1) := $$1 in: (* {c, r} *)
      match: $$1 with:
      { CPLSend ' $0 ' $1 (* {n', m} *) ->
        let: $0 := $(1, 0).+1 in: (* c' *)
        let: $0 := (term_of_nat slc, CSLSend ' $(1, 0) ' ($$0, $(1, 1))) in: (* or *)
        (($$1, $(3, 1)), [$$0], [])
       }
    -} in
  let indication :=
    {-t fun: fun: fun: (* n', s, ii *)
      let: ($0, $1) := $$1 in: (* {c, r} *)
      match: $$1 with:
      { (pattern_of_nat slc, CSLDeliver ' $0 ' ($1, $2)) (* {n, c', m} *) ->
        if: ($0, $1) \in $(1, 1)
        then:
          ($$4, [], [])
        else:
          let: $0 := $(2, 1) :|: [($(1, 0), $(1, 1))] in: (* r' *)
          let: $0 := CPLDeliver ' $(2, 0) ' $(2, 2) in: (* oi *)
          (($(4, 0), $$1), [], [$$0])
       }
    -} in
  let periodic :=
    {-t fun: fun: (* n, s *)
      ($$0, [], [])
    -} in
  Component
    (Logic.eq_refl : term_computable initialize)
    (Logic.eq_refl : term_computable request)
    (Logic.eq_refl : term_computable indication)
    (Logic.eq_refl : term_computable periodic).

(* Lowered stubborn link properties *)
Lemma PL_SL_1 Delta : Context Delta [::] ||- perfect_link, {-A
  forall: forall: forall: (* n, n', m *)
  $$2 \in UCorrect /\ $$1 \in UCorrect ->
  on $$2, event[0]-> CSLSend ' $$1 ' $$0 =>>
  always eventually on $$1, event[0]<- CSLDeliver ' $$2 ' $$0
-}.
Proof.
  duse (DPLower (SL_1 Delta) perfect_link 0 (SL_1_TA Delta));
    rewrite /lower_assertion /=; dclean.

  dforall n; dforall n'; dforall m;
  dforallp n; dforallp n'; dforallp m.
  dif; dswap; difp; [by [] | dswap; dsplitp; dswap; dxchg 0 2].

  eapply DSCut; first (by repeat dclear; apply DTL124 with
    (Ap := {-A Fd <<< [0] -})
    (Ac := {-A eventually on n', event[0]<- CSLDeliver ' n ' m -}));
    dtsubstposp.
  eapply DSCut; first (by repeat dclear; apply DTL124 with
    (Ap := {-A Fd <<< [0] -})
    (Ac := {-A
      on n, event[0]-> CSLSend ' n' ' m ->
      Fd <<< [0] ~> on n', event[0]<- CSLDeliver ' n ' m -}));
    dtsubstposp.
  dtmergeentailsifp.

  dhave {-A
    (Fd <<< [0] /\ on n, event[0]-> CSLSend ' n' ' m) <->
    on n, event[0]-> CSLSend ' n' ' m
  -}.
  {
    dsplit; dif; first by dsplitp; dassumption.
    dsplit; last by [].
    by dsplitp; dclear; dsplitp; dtgenp; dtsubste_l;
      repeat dclear; eapply DPExtension.
  }
  dtgenp; dclean; dtsubstp_l.

  eapply DSCut.
    eapply DTL132 with
      (A1 := {-A on n, event[0]-> CSLSend ' n' ' m -})
      (B1 := {-A Fd <<< [0] -})
      (A2 := {-A on n, event[0]-> CSLSend ' n' ' m -})
      (B2 := {-A Fd <<< [0] =>> eventually on n', event[0]<- CSLDeliver ' n ' m -}).
    difp; first by dsplit; first by
      dtgen; dif; dsplitp; dclear; dsplitp; dtgenp; dtsubste_l;
      repeat dclear; eapply DPExtension.
  eapply DSCut; first (by repeat dclear; eapply DSAndElimSelf with
    (A := {-A on n, event[0]-> CSLSend ' n' ' m -}));
    dtgenp; dclean; dtsubstp_l.
  by eapply DSCut; first (by repeat dclear; eapply DTAndEntails with
    (H := {-A Fd <<< [0] -})
    (A := {-A eventually on n', event[0]<- CSLDeliver ' n ' m -}));
    dtsubstposp.
Qed.

Lemma PL_SL_2 Delta : Context Delta [::] ||- perfect_link, {-A
  forall: forall: forall: (* n, n', m *)
  on $$2, event[0]<- CSLDeliver ' $$1 ' $$0 <~
  on $$1, event[0]-> CSLSend ' $$2 ' $$0
-}.
Proof.
  duse (DPLower (SL_2 Delta) perfect_link 0 (SL_2_TA Delta));
    rewrite /lower_assertion /=; dclean.

  dforall n; dforall n'; dforall m;
  dforallp n; dforallp n'; dforallp m.

  eapply DSCut; first (by repeat dclear; apply DTL124 with
    (Ap := {-A Fd <<< [0] -})
    (Ac := {-A on n, event[0]<- CSLDeliver ' n' ' m ->
      eventuallyp on n', event[0]-> CSLSend ' n ' m -}));
    dtsubstposp.
  dtmergeentailsifp.

  dhave {-A
    (Fd <<< [0] /\ on n, event[0]<- CSLDeliver ' n' ' m) <->
    on n, event[0]<- CSLDeliver ' n' ' m
  -}.
  {
    dsplit; dif; first by dsplitp; dassumption.
    dsplit; last by [].
    by dsplitp; dclear; dsplitp; dtgenp; dtsubste_l;
      repeat dclear; eapply DPExtension.
  }
  by dtgenp; dclean; dtsubstp_l.
Qed.
