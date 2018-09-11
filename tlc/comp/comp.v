From mathcomp.ssreflect
Require Import ssreflect eqtype ssrbool ssrfun seq.
From tlc.utility
Require Import promote variant.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Record subcomp :=
  Subcomp {
    OR : eqType;
    II : eqType;
  }.

Notation subcomps := (seq subcomp) (only parsing).
Definition ORs (scs : subcomps) := map OR scs.
Definition IIs (scs : subcomps) := map II scs.

Section comp.

  Variable node : eqType.

  Record comp (IR OI : eqType) (scs : subcomps) :=
    Comp {
      state : Type;
      init : node -> state;
      output : Type := state * seq (variant (promotes (ORs scs))) * seq OI;
      request : node -> state -> IR -> output;
      indication : node -> state -> variant (promotes (IIs scs)) -> output;
      periodic : node -> state -> output;
    }.

End comp.
