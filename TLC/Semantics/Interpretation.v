Require Import TLC.Concrete.Orientation.
Require Import TLC.Parameters.
Require TLC.Concrete.Component.
Require TLC.Syntax.Component.
Require TLC.Typing.Component.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Record interpretation {P} {C : TLC.Typing.Component.component P} :=
  Interpretation {
    IFn : node P;
    IFd : list nat;
    IFo : orientation;
    IFe : TLC.Concrete.Component.event
      (TLC.Syntax.Component.concrete_component
        (TLC.Typing.Component.syntactic_component C));
    IFors : list
      (TLC.Concrete.Component.or_event
        (TLC.Syntax.Component.concrete_component
          (TLC.Typing.Component.syntactic_component C)));
    IFois : list
      (TLC.Concrete.Component.oi_event
        (TLC.Syntax.Component.concrete_component
          (TLC.Typing.Component.syntactic_component C)));
    IFs : TLC.Concrete.Component.states
      (TLC.Syntax.Component.concrete_component
        (TLC.Typing.Component.syntactic_component C));
    IFs' : TLC.Concrete.Component.states
      (TLC.Syntax.Component.concrete_component
        (TLC.Typing.Component.syntactic_component C));
    INodes : list (node P);
    ICorrectNodes : list (node P);
  }.

Arguments interpretation : clear implicits.
Arguments interpretation {P} C.

(* Notations for interpretations *)
Notation "[I: x ]" := (interpretation x) (at level 0) : type_scope.
