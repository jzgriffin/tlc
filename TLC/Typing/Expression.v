Require Import TLC.Syntax.Constant.
Require Import TLC.Syntax.Expression.
Require Import TLC.Syntax.Flexible.
Require Import TLC.Typing.Component.
Require Import TLC.Typing.Context.
Require Import TLC.Typing.Type.
Require Import TLC.Utility.HList.

Section typed_expression.

  Reserved Notation "x |- y : z" (at level 0, no associativity, y at level 99).

  (* Type-checked expression terms *)
  Inductive typed_expression {P} {C : component P} :
    forall G : context, type -> expression -> Type :=
  (* Variables *)
  | TEVariable {G t} (m : hmember t G) n :
    hoffset m = n ->
    G |- $n : t
  (* Constants *)
  | TECUnit {G} : G |- ^CUnit : TUnit
  (* Products *)
  | TECPair {G t1 t2} : G |- ^CPair : (t1 -> t2 -> t1 * t2)
  (* Sums *)
  | TECLeft {G t1 t2} : G |- ^CLeft : (t1 -> t1 + t2)
  | TECRight {G t1 t2} : G |- ^CRight : (t2 -> t1 + t2)
  (* Lists *)
  | TECNil {G t1} : G |- ^CNil : (TList t1)
  | TECCons {G t1} : G |- ^CCons : (t1 -> TList t1 -> TList t1)
  (* Naturals *)
  | TECZero {G} : G |- ^CZero : TNatural
  | TECSucc {G} : G |- ^CSucc : (TNatural -> TNatural)
  (* Orientations *)
  | TECORequest {G} : G |- ^CORequest : TOrientation
  | TECOIndication {G} : G |- ^COIndication : TOrientation
  | TECOPeriodic {G} : G |- ^COPeriodic : TOrientation
  (* Model *)
  | TECNodes {G} : G |- ^CNodes : (TList TNode)
  | TECCorrectNodes {G} : G |- ^CCorrectNodes : (TList TNode)
  (* Periodic events *)
  | TECPE {G} : G |- ^CPE : TPEvent
  (* Fair-loss link request *)
  | TECFLLSend {G} : G |- ^CFLLSend : (TNode -> TMessage -> TFLLRequest)
  (* Fair-loss link indication *)
  | TECFLLDeliver {G} : G |- ^CFLLDeliver :
    (TNode -> TMessage -> TFLLIndication)
  (* Stubborn link request *)
  | TECSLSend {G} : G |- ^CSLSend : (TNode -> TMessage -> TSLRequest)
  (* Stubborn link indication *)
  | TECSLDeliver {G} : G |- ^CSLDeliver : (TNode -> TMessage -> TSLIndication)
  (* Stubborn link functions *)
  | TECSLInitialize {G} : G |- ^CSLInitialize : (TNode -> TSLState)
  | TECSLRequest {G} : G |- ^CSLRequest :
    (TNode -> TSLState -> TSLRequest ->
      (TSLState * TList TFLLRequest * TList TSLIndication))
  | TECSLIndication {G} : G |- ^CSLIndication :
    (TNode -> TSLState -> TFLLIndication ->
      (TSLState * TList TFLLRequest * TList TSLIndication))
  | TECSLPeriodic {G} : G |- ^CSLPeriodic :
    (TNode -> TSLState ->
      (TSLState * TList TFLLRequest * TList TSLIndication))
  (* Flexible variables *)
  | TEFn {G} : G |- `Fn : TNode
  | TEFd {G} : G |- `Fd : (TList TNatural)
  | TEFo {G} : G |- `Fo : TOrientation
  | TEFe {G} : G |- `Fe : (event C)
  | TEFors {G} : G |- `Fors : (TList (or_event C))
  | TEFois {G} : G |- `Fois : (TList (oi_event C))
  | TEFs {G} : G |- `Fs : (states C)
  | TEFs' {G} : G |- `Fs' : (states C)
  (* Application *)
  | TEApplication {G t1 t2} e1 e2 :
    G |- e1 : (t1 -> t2) ->
    G |- e2 : t1 ->
    G |- (e1 <- e2) : t2
  where "x |- y : z" := (typed_expression x z y) : type_scope.

End typed_expression.

Arguments typed_expression : clear implicits.
Arguments typed_expression {P} C.

Notation "x |-e y : z | w" := (typed_expression w x z y)
  (at level 0, no associativity, y at level 99) : type_scope.
