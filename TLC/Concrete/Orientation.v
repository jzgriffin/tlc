Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Orientation of events in the logic *)
Inductive orientation : Type :=
| ORequest
| OIndication
| OPeriodic.
