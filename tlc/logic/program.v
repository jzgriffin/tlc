From mathcomp.ssreflect
Require Import ssreflect eqtype ssrbool seq fintype.
From tlc.utility
Require Import seq.
From tlc.comp
Require Import component.
From tlc.assert
Require Import all_assert.
From tlc.logic
Require Import sequent.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Basic rules of the program logic *)
Section basic.

  Reserved Notation "|- A"
    (at level 80, no associativity).

  Inductive program {C : component} : seq (@prop C) -> @prop C -> Prop :=
  | PSequent X A : sequent X A -> program X A (* Program extends sequent *)
  | PNode : |- TLC.PNode
  | PIR (e : @term C IREvent) : |- TLC.PIR e
  | PII (i : 'I_(size (@IIEvents C))) (e : @term C (ith i)) : |- TLC.PII e
  | PPe : |- TLC.PPe
  | POR (n : @term C Node) (i : 'I_(size (@OREvents C))) (e : @term C (ith i)) :
    |- TLC.POR n e
  | POI (n : @term C Node) (e : @term C OIEvent) : |- TLC.POI n e
  | POR' (n : @term C Node) (i : 'I_(size (@OREvents C)))
    (e : @term C (ith i)) : |- TLC.POR' n e
  | POI' (n : @term C Node) (e : @term C OIEvent) : |- TLC.POI' n e
  | PInit (n : @term C Node) : |- TLC.PInit n
  | PPostPre (n : @term C Node) (s : @term C State) : |- TLC.PPostPre n s
  | PSeq (n : @term C Node) : |- TLC.PSeq n
  | PASelf : |- TLC.PASelf
  (* TODO: PLSInv *)
  | PCSet (n : @term C Node) : |- TLC.PCSet n
  | PAPer (n : @term C Node) : |- TLC.PAPer n
  | PFLoss (ir : 'I_(size (@OREvents C))) (ii : 'I_(size (@IIEvents C)))
    (Hr : ith ir = FLRequest) (Hi : ith ii = FLIndication)
    (n n' : @term C Node) (m : @term C Message) :
    |- TLC.PFLoss Hr Hi n n' m
  | PFDup (ir : 'I_(size (@OREvents C))) (ii : 'I_(size (@IIEvents C)))
    (Hr : ith ir = FLRequest) (Hi : ith ii = FLIndication)
    (n n' : @term C Node) (m : @term C Message) :
    |- TLC.PFDup Hr Hi n n' m
  | PNForge (ir : 'I_(size (@OREvents C))) (ii : 'I_(size (@IIEvents C)))
    (Hr : ith ir = FLRequest) (Hi : ith ii = FLIndication)
    (n n' : @term C Node) (m : @term C Message) :
    |- TLC.PNForge Hr Hi n n' m
  | PUniOR (n : @term C Node) (i : 'I_(size OREvents)) (e : @term C (ith i)) :
    |- TLC.PUniOR n e
  | PUniOI (n : @term C Node) (e : @term C OIEvent) :
    |- TLC.PUniOI n e
  where "|- A" := (program [::] A).

End basic.

Notation "X |- C , A" :=
  (@program C X A)
  (at level 80, no associativity).
