From mathcomp.ssreflect
Require Import ssreflect eqtype ssrbool seq.
From tlc.utility
Require Import seq.

Require Import variable constant function term predicate assertion.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Inductive SelfInvariant' : assertion -> Prop :=
| SelfInvariant'_correct t :
  SelfInvariant' (Apred Pcorrect [:: t])
| SelfInvariant'_req_ev n e :
  SelfInvariant' (Aon n (Aev Cnil Creq_ev e))
| SelfInvariant'_ind_ev n e :
  SelfInvariant' (Aon n (Aev (term_seq [:: Tvar Vri]) Cind_ev e))
| SelfInvariant'_per_ev n e :
  SelfInvariant' (Aon n (Aev Cnil Cper_ev e))
| SelfInvariant'_conj A1 A2 :
  SelfInvariant' A1 ->
  SelfInvariant' A2 ->
  SelfInvariant' (Aconj A1 A2)
| SelfInvariant'_neg A :
  SelfInvariant' A ->
  SelfInvariant' (Aneg A)
| SelfInvariant'_univ x A :
  SelfInvariant' A ->
  SelfInvariant' (Auniv x A)
| SelfInvariant'_alwaysfs A :
  SelfInvariant' A ->
  SelfInvariant' (Aalwaysfs A)
| SelfInvariant'_alwaysps A :
  SelfInvariant' A ->
  SelfInvariant' (Aalwaysps A)
| SelfInvariant'_eventfs A :
  SelfInvariant' A ->
  SelfInvariant' (Aeventfs A)
| SelfInvariant'_eventps A :
  SelfInvariant' A ->
  SelfInvariant' (Aeventps A).

Inductive SelfInvariant : assertion -> Prop :=
| SelfInvariant_alwaysf A :
  SelfInvariant' A ->
  SelfInvariant (Aalwaysf A).
