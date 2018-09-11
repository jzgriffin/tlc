From mathcomp.ssreflect
Require Import ssreflect eqtype seq.
From tlc.assert
Require Import all_assert.
From tlc.comp
Require Import comp.

Require Import sequent.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section program_basic.

  Import AssertNotations.

  Variable node : eqType.
  Variable IR : eqType.
  Variable OI : eqType.
  Variable scs : subcomps.
  Variable c : @comp node IR OI scs.

  Axiom pl_node :
    [::] |- c, (alwaysf: (Pin?(Vrn, Cnat_set))%A)%A.
  (* TODO: pl_ir *)
  (* TODO: pl_ii *)
  (* TODO: pl_pe *)
  (* TODO: pl_or *)
  (* TODO: pl_oi *)
  (* TODO: pl_or' *)
  (* TODO: pl_oi' *)
  (* TODO: pl_init *)
  (* TODO: pl_postpre *)
  (* TODO: pl_seq *)
  Axiom pl_aself :
    [::] |- c, (self: alwaysf: self_ev)%A.
  (* TODO: pl_sinv *)
  (* TODO: pl_cset *)
  (* TODO: pl_aper *)
  (* TODO: pl_floss *)
  (* TODO: pl_fdup *)
  (* TODO: pl_nforge *)
  (* TODO: pl_unior *)
  (* TODO: pl_unioi *)

End program_basic.
