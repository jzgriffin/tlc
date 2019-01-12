Require Import TLC.Syntax.Constant.
Require TLC.Concrete.Component.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module CC := TLC.Concrete.Component.

(* Type of individual syntactic components *)
Record component {P} : Type :=
  Component {
    concrete_component : CC.component P;
    (* Functions *)
    initialize : constant;
    request : constant;
    indication : constant;
    periodic : constant;
  }.

Arguments component : clear implicits.
