Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section fair_loss_link.

  Variable node : Type.
  Variable message : Type.

  Inductive request_fl : Type :=
  | Send_fl : node -> message -> request_fl.

  Inductive indication_fl : Type :=
  | Deliver_fl : node -> message -> indication_fl.

End fair_loss_link.
