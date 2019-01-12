Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Constant terms of the language *)
Inductive constant : Type :=
| CUnit
(* Products *)
| CPair
(* Sums *)
| CLeft
| CRight
(* Lists *)
| CNil
| CCons
(* Naturals *)
| CZero
| CSucc
(* Orientations *)
| CORequest
| COIndication
| COPeriodic
(* Model *)
| CNodes
| CCorrectNodes
(* Periodic events *)
| CPE
(* Fair-loss link request *)
| CFLLSend
(* Fair-loss link indication *)
| CFLLDeliver
(* Stubborn link request *)
| CSLSend
(* Stubborn link indication *)
| CSLDeliver
(* Stubborn link functions *)
| CSLInitialize
| CSLRequest
| CSLIndication
| CSLPeriodic.

(* Decidable equality *)
Lemma constant_eq_dec (c c' : constant) : {c = c'} + {c <> c'}.
Proof.
  decide equality.
Defined.

Definition constant_eqb c c' :=
  match c, c' with
  | CUnit, CUnit => true
  (* Products *)
  | CPair, CPair => true
  (* Sums *)
  | CLeft, CLeft => true
  | CRight, CRight => true
  (* Lists *)
  | CNil, CNil => true
  | CCons, CCons => true
  (* Naturals *)
  | CZero, CZero => true
  | CSucc, CSucc => true
  (* Orientations *)
  | CORequest, CORequest => true
  | COIndication, COIndication => true
  | COPeriodic, COPeriodic => true
  (* Model *)
  | CNodes, CNodes => true
  | CCorrectNodes, CCorrectNodes => true
  (* Periodic events *)
  | CPE, CPE => true
  (* Fair-loss link request *)
  | CFLLSend, CFLLSend => true
  (* Fair-loss link indication *)
  | CFLLDeliver, CFLLDeliver => true
  (* Stubborn link request *)
  | CSLSend, CSLSend => true
  (* Stubborn link indication *)
  | CSLDeliver, CSLDeliver => true
  (* Stubborn link functions *)
  | CSLInitialize, CSLInitialize => true
  | CSLRequest, CSLRequest => true
  | CSLIndication, CSLIndication => true
  | CSLPeriodic, CSLPeriodic => true
  | _, _ => false
  end.

Lemma constant_eqb_refl c : constant_eqb c c = true.
Proof.
  now destruct c.
Qed.
