From mathcomp.ssreflect
Require Import ssreflect seq fintype.
From tlc.utility
Require Import seq.
From tlc.comp
Require Import component.
From tlc.assert
Require Import all_assert.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Basic rules of the program logic *)
Section basic.

  Reserved Notation "X |- p"
    (at level 80, no associativity).

  Import TLC.

  Inductive program {C} : seq (@prop C) -> @prop C -> Prop :=

  | PNode X : X |-
    (henceforth: Atom (mem <- Fn <- Nodes))

  | PIR X (e : @term C IREvent) : X |-
    (event: [], Request, EventIR <- e =>>
    (Fs' <- Fn, Fors, Fois) = request <- Fn <- (Fs <- Fn) <- e)

  | PII X (i : 'I_(size (@IIEvents C))) (e : @term C (ith i)) : X |-
    let: ie := @Const C Nat i in
    let: ei := ini i <- e in
    (event: [ie], Indication, EventII <- ei =>>
    (Fs' <- Fn, Fors, Fois) = indication <- Fn <- (Fs <- Fn) <- ei)

  | PPe X : X |-
    (event: [], Periodic, per =>>
    (Fs' <- Fn, Fors, Fois) = periodic <- Fn <- (Fs <- Fn))

  | POR X (n : @term C Node)
  (i : 'I_(size (@OREvents C))) (e : @term C (ith i)) : X |-
    let: ie := @Const C Nat i in
    let: ei := ini i <- e in
    (on: n, (Atom (mem <- ei <- Fors) /\ self) =>>
    eventually^: on: n, event: [ie], Request, EventOR <- ei)

  | POI X (n : @term C Node) (e : @term C OIEvent) : X |-
    (on: n, (Atom (mem <- e <- Fois) /\ self) =>>
    eventually^: on: n, event: [], Indication, EventOI <- e)

  | POR' X (n : @term C Node)
  (i : 'I_(size (@OREvents C))) (e : @term C (ith i)) : X |-
    let: ie := @Const C Nat i in
    let: ei := ini i <- e in
    (on: n, event: [ie], Request, EventOR <- ei =>>
    once^: on: n, (Atom (mem <- ei <- Fors) /\ self))

  | POI' X (n : @term C Node) (e : @term C OIEvent) : X |-
    (on: n, event: [], Indication, EventOI <- e =>>
    once^: on: n, (Atom (mem <- e <- Fois) /\ self))

  | PInit X (n : @term C Node) : X |-
    (self: (Fs <- n = init <- n))

  | PPostPre X (n : @term C Node) (s : @term C State) : X |-
    (self: (Atom (mem <- n <- Nodes) ->
      (Fs' <- n = s <=> next: (Fs <- n = s))))

  | PSeq X (n : @term C Node) : X |-
    (~(Fn = n) =>> (Fs' <- n = Fs <- n))

  | PASelf X : X |-
    (self: henceforth: self)

  (* TODO: PSInv *)

  | PCSet X (n : @term C Node) : X |-
    ((Atom (correct <- n)) <-> (Atom (mem <- n <- Correct)))

  | PAPer X (n : @term C Node) : X |-
    ((Atom (mem <- n <- Correct)) ->
    henceforth: eventually: on: n, event: [], Periodic, per)

  | PFLoss X
  (ir : 'I_(size (@OREvents C))) (ii : 'I_(size (@IIEvents C)))
  (Hr : ith ir = FLRequest) (Hi : ith ii = FLIndication)
  (n n' : @term C Node) (m : @term C Message) : X |-
    let: ier := @Const C Nat ir in
    let: iei := @Const C Nat ii in
    ((Atom (correct <- n')) ->
    henceforth: eventually: on: n, event: [ier], Request,
      (EventOR <- (ini ir <- (ith_FLRequest Hr (Send_fl <- n' <- m)))) ->
    henceforth: eventually: on: n', event: [iei], Indication,
      (EventII <- (ini ii <- (ith_FLIndication Hi (Deliver_fl <- n' <- m)))))

  | PFDup X
  (ir : 'I_(size (@OREvents C))) (ii : 'I_(size (@IIEvents C)))
  (Hr : ith ir = FLRequest) (Hi : ith ii = FLIndication)
  (n n' : @term C Node) (m : @term C Message) : X |-
    let: ier := @Const C Nat ir in
    let: iei := @Const C Nat ii in
    (henceforth: eventually: on: n', event: [iei], Indication,
      (EventII <- (ini ii <- (ith_FLIndication Hi (Deliver_fl <- n' <- m)))) ->
    henceforth: eventually: on: n, event: [ier], Request,
      (EventOR <- (ini ir <- (ith_FLRequest Hr (Send_fl <- n' <- m)))))

  | PNForge X
  (ir : 'I_(size (@OREvents C))) (ii : 'I_(size (@IIEvents C)))
  (Hr : ith ir = FLRequest) (Hi : ith ii = FLIndication)
  (n n' : @term C Node) (m : @term C Message) : X |-
    let: ier := @Const C Nat ir in
    let: iei := @Const C Nat ii in
    ((on: n', event: [iei], Indication,
      (EventII <- (ini ii <-
        (ith_FLIndication Hi (Deliver_fl <- n' <- m))))) =>>
    once: on: n, event: [ier], Request,
      (EventOR <- (ini ir <- (ith_FLRequest Hr (Send_fl <- n' <- m)))))

  | PUniOR X (n : @term C Node)
  (i : 'I_(size OREvents)) (e : @term C (ith i)) : X |-
    let: ie := @Const C Nat i in
    let: ei := ini i <- e in
    (((occ <- ei <- Fors) <= (@Const _ Nat 1) /\
      alwaysbeen^: (Fn = n /\ self -> ~(Atom (mem <- ei <- Fors))) /\
      henceforth^: (Fn = n /\ self -> ~(Atom (mem <- ei <- Fors)))) =>>
    (on: n, event: [], Indication, EventOR <- ei) =>>
    ((alwaysbeen^: ~(on: n, event: [ie], Request, EventOR <- ei)) /\
      (henceforth^: ~(on: n, event: [ie], Request, EventOR <- ei))))

  | PUniOI X (n : @term C Node) (e : @term C OIEvent) : X |-
    (((occ <- e <- Fois) <= (@Const _ Nat 1) /\
      alwaysbeen^: (Fn = n /\ self -> ~(Atom (mem <- e <- Fois))) /\
      henceforth^: (Fn = n /\ self -> ~(Atom (mem <- e <- Fois)))) =>>
    (on: n, event: [], Indication, EventOI <- e) =>>
    ((alwaysbeen^: ~(on: n, event: [], Indication, EventOI <- e)) /\
      (henceforth^: ~(on: n, event: [], Indication, EventOI <- e))))

  where "X |- p" := (program X p).

End basic.

Notation "X |-p C , p" := (@program C X p)
  (at level 80, no associativity).
