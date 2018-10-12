From Coq.Lists
Require Import List.
From mathcomp.ssreflect
Require Import ssreflect eqtype ssrbool ssrnat seq fintype.
From tlc.utility
Require Import seq variant lemmas.
From tlc.comp
Require Import p_event component flc.
From tlc.assert
Require Import scope orientation type flexible_var rigid_var term atom prop.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* TODO: Placeholdes *)
Definition correct {C} (n : node C) : bool := true.
Definition Correct {C} : seq (node C) := [::].
Definition Nodes {C} : seq (node C) := [::].

Fixpoint denote_eq {C} t : @denote_type C (t -> t -> Bool) :=
  let: t' := @denote_type C t in
  match t with
  | Unit => fun x y => true
  | Func t1 t2 => fun x y => x == y
  | Product t1 t2 =>
    fun x y => (denote_eq (fst x) (fst y)) && (denote_eq (snd x) (snd y))
  | Sum t1 t2 =>
    fun x y =>
      match x, y with
      | inl x', inl y' => denote_eq x' y'
      | inr x', inr y' => denote_eq x' y'
      | _, _ => false
      end
  | List t' =>
    fix e x y :=
      match x, y with
      | [::], [::] => true
      | x1 :: s1', x2 :: s2' => denote_eq x1 x2 && e s1' s2'
      | _, _ => false
      end
  | Bool => fun x y => x == y
  | Nat => fun x y => x == y
  | Node => fun x y => x == y
  | Message => fun x y => x == y
  | FLRequest => fun x y => x == y
  | FLIndication => fun x y => x == y
  | Orientation => fun x y => x == y
  | IREvent => fun x y => x == y
  | OIEvent => fun x y => x == y
  | OREvent' _ => fun x y => x == y
  | IIEvent' _ => fun x y => x == y
  | PEvent => fun x y => x == y
  | State => fun x y => x == y
  end.

Module TLC.

Section event.

  (* Constructors for events *)
  Definition Send_fl {C} :=
    @Const C (Node -> Message -> FLRequest) Send_fl.
  Definition Deliver_fl {C} :=
    @Const C (Node -> Message -> FLIndication) Deliver_fl.
  Definition EventIR {C} :=
    @Const C (IREvent -> Event) (fun x => inl (inl (inl (inl x)))).
  Definition EventOI {C} :=
    @Const C (OIEvent -> Event) (fun x => inl (inl (inl (inr x)))).
  Definition EventOR {C} :=
    @Const C (OREvent -> Event) (fun x => inl (inl (inr x))).
  Definition EventII {C} :=
    @Const C (IIEvent -> Event) (fun x => inl (inr x)).
  Definition per {C} :=
    @Const C Event (inr per).

End event.

(* Equality of terms *)
Section eq.

  Definition eq {C t} :=
    @Const C _ (@denote_eq C t).
  Definition Eq {C t} (x y : @term C t) : atom :=
    eq <- x <- y.

End eq.

(* Notation for term equality *)
Notation "x = y" :=
  (Eq x y)
  (at level 70, no associativity) : tlc_core_scope.

(* Boolean constants *)
Section bool.

  Definition true {C} := @Const C Bool true.
  Definition false {C} := @Const C Bool false.

End bool.

(* Product functions *)
Section product.

  Definition pair {C t1 t2} :=
    @Const C (t1 -> t2 -> t1 * t2) pair.

End product.

(* Notations for building products *)
Notation "( x , y , .. , z )" :=
  (pair <- (.. (pair <- x <- y) ..) <- z)%tlc
  : tlc_core_scope.

(* Sum functions *)
Section sum.

  Definition inl {C t1 t2} :=
    @Const C (t1 -> t1 + t2) inl.
  Definition inr {C t1 t2} :=
    @Const C (t2 -> t1 + t2) inr.

  Definition ini {C} {ts : seq (@type C)} (i : 'I_(size ts)) :
    @term C (ith i -> Variant ts).
    case Hts: ts i => [ | t ts'] i; case Hi: i => [n Hs];
    case Hn: n Hs Hi => [ | n'] Hs Hi; try by [];
    apply Const; rewrite denote_func denote_variant;
    remember [seq denote_type t | t <- ts] as Ts;
    have H: (size Ts = size ts) by subst Ts; exact: size_map.
    - (* ts = t :: ts', n = 0 *)
      assert (HeqTs' := HeqTs); rewrite Hts /= in HeqTs'.
      have HS: (0 < size Ts) by rewrite HeqTs'.
      rewrite HeqTs' in HS; pose I := Ordinal HS.
      have Ht: (denote_type t = ith I) by subst I; exact: ith0.
      rewrite ith0 Ht -Hts -HeqTs HeqTs'; exact: eq_ini.
    - (* ts = t :: ts', n = n'.+1 *)
      assert (HeqTs' := HeqTs); rewrite Hts /= in HeqTs'.
      have HS: (n'.+1 < size Ts) by rewrite HeqTs /= size_map Hts //.
      rewrite HeqTs' in HS; pose I := Ordinal HS.
      have Ht: (denote_type (ith i) = ith I).
        subst i I; move: HS; rewrite -map_cons => HS; exact: ith_map.
      rewrite -Hi Ht -Hts -HeqTs HeqTs'; exact: eq_ini.
  Unshelve. apply Ts.
  Defined.

End sum.

(* List constants and functions *)
Section list.

  Definition nil {C t} :=
    @Const C [t] nil.
  Definition cons {C t} :=
    @Const C (t -> [t] -> [t]) cons.
  Definition rcons {C t} :=
    @Const C ([t] -> t -> [t]) rcons.

  Definition mem {C t} :=
    @Const C (t -> [t] -> Bool) (fun x s => has (@denote_eq C t x) s).
  Definition occ {C t} :=
    @Const C (t -> [t] -> Nat) (fun x s => count (@denote_eq C t x) s).

End list.

(* Notations for building lists *)
Notation "[ ]" :=
  nil
  : tlc_core_scope.
Notation "[ x ]" :=
  (cons <- x <- nil)%tlc
  : tlc_core_scope.
Notation "[ x ; y ; .. ; z ]" :=
  (cons <- x <- (cons <- y <- (.. (cons <- z <- nil) ..)))%tlc
  : tlc_core_scope.

(* Natural functions *)
Section nat.

  Definition ltn {C} :=
    @Const C (Nat -> Nat -> Bool) (fun x y => x < y).
  Definition len {C} (x y : @term C Nat) : @prop C :=
    Atom (ltn <- x <- y) \/ x = y.
  Definition gtn {C} (x y : @term C Nat) : @prop C :=
    ~(len x y).
  Definition gen {C} (x y : @term C Nat) : @prop C :=
    gtn x y \/ x = y.

End nat.

(* Notations for natural comparisons *)
Notation "x < y" :=
  (ltn <- x <- y)%tlc
  : tlc_core_scope.
Notation "x <= y" :=
  (len x y)%tlc
  : tlc_core_scope.
Notation "x > y" :=
  (gtn x y)%tlc
  : tlc_core_scope.
Notation "x >= y" :=
  (gen x y)%tlc
  : tlc_core_scope.

(* Orientation constants *)
Section orientation.

  Definition Request {C} := @Const C Orientation Request.
  Definition Indication {C} := @Const C Orientation Indication.
  Definition Periodic {C} := @Const C Orientation Periodic.

End orientation.

(* Correct node classification *)
Section correct.

  (* TODO: Holes *)
  Definition correct {C} := @Const C (Node -> Bool) correct.
  Definition Correct {C} := @Const C [Node] Correct.
  Definition Nodes {C} := @Const C [Node] Nodes.

End correct.

(* Flexible variables *)
Section flexible.

  Definition Fn {C} := @Flexible C Fn.
  Definition Fd {C} := @Flexible C Fd.
  Definition Fo {C} := @Flexible C Fo.
  Definition Fe {C} := @Flexible C Fe.
  Definition Fors {C} := @Flexible C Fors.
  Definition Fois {C} := @Flexible C Fois.
  Definition Fs {C} := @Flexible C Fs.
  Definition Fs' {C} := @Flexible C Fs'.

End flexible.

(* Component types and functions *)
Section component.

  (* Event handler functions *)
  Definition Output {C} : @type C := State * [OREvent] * [OIEvent].
  Definition init {C} :=
    @Const C (Node -> State) (@init C).
  Definition request {C} : @term C (Node -> State -> IREvent -> Output).
    apply Const; rewrite /= denote_or_event.
    by exact: request.
  Defined.
  Definition indication {C} : @term C (Node -> State -> IIEvent -> Output).
    apply Const; rewrite /= denote_ii_event denote_or_event.
    by exact: indication.
  Defined.
  Definition periodic {C} : @term C (Node -> State -> Output).
    apply Const; rewrite /= denote_or_event.
    by exact: periodic.
  Defined.

End component.

(* Syntactic sugar for events *)
Section sugar.

  Definition On {C} n A : @prop C :=
    Fn = n /\ A.
  Definition Ev {C} d o e : @prop C :=
    Fd = d /\ Fo = o /\ Fe = e.
  Definition SelfEv {C} : @prop C :=
    let: request_ev := Fd = nil /\ Fo = Request in
    let: periodic_ev := Fd = nil /\ Fo = Periodic in
    let: indication_ev :=
      let: i := RigidVar Nat 0 in
      always: i, (Fd = [Rigid i] /\ Fo = Indication) in
    request_ev \/ periodic_ev \/ indication_ev.

End sugar.

(* Notations for syntactic sugars *)
Notation "'on:' n , P" :=
  (On n P)
  (at level 65, right associativity) : tlc_core_scope.
Notation "'ev:' d , o , e" :=
  (Ev d o e)
  (at level 65, right associativity) : tlc_core_scope.
Notation "'self'" := (SelfEv)
  : tlc_core_scope.

(* Basic program logic rules *)
Definition PNode {C} : @prop C :=
  alwaysf: Atom (mem <- Fn <- Nodes).
Definition PIR {C} (e : @term C IREvent) : @prop C :=
  ev: [], Request, EventIR <- e =>:
  (Fs' <- Fn, Fors, Fois) = request <- Fn <- (Fs <- Fn) <- e.
Definition PII {C} (i : 'I_(size (@IIEvents C))) (e : @term C (ith i))
: @prop C :=
  let: ie := @Const C Nat i in
  let: ei := ini i <- e in
  ev: [ie], Indication, EventII <- ei =>:
  (Fs' <- Fn, Fors, Fois) = indication <- Fn <- (Fs <- Fn) <- ei.
Definition PPe {C} : @prop C :=
  ev: [], Periodic, per =>:
  (Fs' <- Fn, Fors, Fois) = periodic <- Fn <- (Fs <- Fn).
Definition POR {C} (n : @term C Node)
(i : 'I_(size (@OREvents C))) (e : @term C (ith i)) : @prop C :=
  let: ie := @Const C Nat i in
  let: ei := ini i <- e in
  on: n, (Atom (mem <- ei <- Fors) /\ self) =>:
  existsf^: on: n, ev: [ie], Request, EventOR <- ei.
Definition POI {C} (n : @term C Node) (e : @term C OIEvent) : @prop C :=
  on: n, (Atom (mem <- e <- Fois) /\ self) =>:
  existsf^: on: n, ev: [], Indication, EventOI <- e.
Definition POR' {C} (n : @term C Node)
(i : 'I_(size (@OREvents C))) (e : @term C (ith i)) : @prop C :=
  let: ie := @Const C Nat i in
  let: ei := ini i <- e in
  on: n, ev: [ie], Request, EventOR <- ei =>:
  existsp^: on: n, (Atom (mem <- ei <- Fors) /\ self).
Definition POI' {C} (n : @term C Node) (e : @term C OIEvent) : @prop C :=
  on: n, ev: [], Indication, EventOI <- e =>:
  existsp^: on: n, (Atom (mem <- e <- Fois) /\ self).
Definition PInit {C} (n : @term C Node) : @prop C :=
  self: (Fs <- n = init <- n).
Definition PPostPre {C} (n : @term C Node) (s : @term C State) : @prop C :=
  self: (Atom (mem <- n <- Nodes) ->
    (Fs' <- n = s <=>: next: (Fs <- n = s))).
Definition PSeq {C} (n : @term C Node) : @prop C :=
  ~(Fn = n) =>: (Fs' <- n = Fs <- n).
Definition PASelf {C} : @prop C :=
  self: alwaysf: self.
(* TODO: PLSInv; need restrict *)
Definition PCSet {C} (n : @term C Node) : @prop C :=
  (Atom (correct <- n)) <-> (Atom (mem <- n <- Correct)).
Definition PAPer {C} (n : @term C Node) : @prop C :=
  (Atom (mem <- n <- Correct)) ->
  alwaysf: existsf: on: n, ev: [], Periodic, per.
Lemma InP (T : eqType) (x : T) (s : seq T) : reflect (In x s) (x \in s).
  (* TODO *)
Admitted.
Definition PFLoss {C}
(Hr : In req_fl (@or_events C))
(Hi : In ind_fl (@ii_events C))
(n n' : @term C Node) (m : @term C Message) : @prop C :=
  let: ir := ith (findex (Hr) in
  let: ii := ith (findex Hi) in
  let: ie := @Const C Nat ir in
  (Atom (correct <- n')) ->
  alwaysf: existsf: on: n, ev: [ie], Request, (Send_fl <- n' <- m) ->
  alwaysf: existsf: on: n', ev: [ie], Indication, (Deliver_fl <- n <- m).
*)
(* TODO: PLFDup; how to construct events from FLC *)
(* TODO: PLNForge; how to construct events from FLC *)
Definition PUniOR {C} (n : @term C Node)
(i : 'I_(size OREvents)) (e : @term C (ith i)) : @prop C :=
  let: ie := @Const C Nat i in
  let: ei := ini i <- e in
  ((occ <- ei <- Fors) <= (@Const _ Nat 1) /\
    alwaysp^: (Fn = n /\ self -> ~(Atom (mem <- ei <- Fors))) /\
    alwaysf^: (Fn = n /\ self -> ~(Atom (mem <- ei <- Fors)))) =>:
  (on: n, ev: [], Indication, EventOR <- ei) =>:
  ((alwaysp^: ~(on: n, ev: [ie], Request, EventOR <- ei)) /\
    (alwaysf^: ~(on: n, ev: [ie], Request, EventOR <- ei))).
Definition PUniOI {C} (n : @term C Node) (e : @term C OIEvent) : @prop C :=
  ((occ <- e <- Fois) <= (@Const _ Nat 1) /\
    alwaysp^: (Fn = n /\ self -> ~(Atom (mem <- e <- Fois))) /\
    alwaysf^: (Fn = n /\ self -> ~(Atom (mem <- e <- Fois)))) =>:
  (on: n, ev: [], Indication, EventOI <- e) =>:
  ((alwaysp^: ~(on: n, ev: [], Indication, EventOI <- e)) /\
    (alwaysf^: ~(on: n, ev: [], Indication, EventOI <- e))).

End TLC.

(* Constructs a list of constant terms from a sequence of values *)
Fixpoint seq_to_term {C} t (xs : seq (@denote_type C t)) :=
  match xs with
  | nil => TLC.nil
  | x :: xs' => App (App TLC.cons (@Const C t x)) (seq_to_term xs')
  end.
