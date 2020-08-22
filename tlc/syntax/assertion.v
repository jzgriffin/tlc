(* TLC in Coq
 *
 * Module: tlc.syntax.assertion
 * Purpose: Contains the syntax of assertions.
 *)

Require Import mathcomp.ssreflect.eqtype.
Require Import mathcomp.ssreflect.seq.
Require Import mathcomp.ssreflect.ssrbool.
Require Import mathcomp.ssreflect.ssreflect.
Require Import mathcomp.ssreflect.ssrnat.
Require Import tlc.operation.orientation.
Require Import tlc.syntax.constructor.
Require Import tlc.syntax.flexible.
Require Import tlc.syntax.function.
Require Import tlc.syntax.parameter.
Require Import tlc.syntax.predicate.
Require Import tlc.syntax.term.
Require Import tlc.syntax.unknown.
Require Import tlc.syntax.variable.
Require Import tlc.utility.seq.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Forms of logical assertions *)
Inductive assertion :=
(* Predicate logic *)
| AFalse
| APredicate (p : predicate) (* Predicates *)
| ANot (A : assertion) (* Negation *)
| AAnd (A1 A2 : assertion) (* Conjunction *)
| AForAll (A : assertion) (* Universal quantification *)
| AApplication (A : assertion) (t : term) (* Universal instantiation *)
(* Temporal logic *)
| AAlways' (A : assertion) (* Always strictly in the future *)
| AAlwaysP' (A : assertion) (* Always strictly in the past *)
| AEventually' (A : assertion) (* Eventually strictly in the future *)
| AEventuallyP' (A : assertion) (* Eventually strictly in the past *)
| ANext (A : assertion) (* In the next label *)
| APrevious (A : assertion) (* In the previous label *)
| ASelf (A : assertion). (* Subtrace of self events *)

(* Equality *)
Section eq.

  (* Boolean equality *)
  Fixpoint assertion_eq A1 A2 :=
    match A1, A2 with
    (* Predicate logic *)
    | AFalse, AFalse => true
    | APredicate p1, APredicate p2 => p1 == p2
    | ANot A1, ANot A2 => assertion_eq A1 A2
    | AAnd A1_1 A1_2, AAnd A2_1 A2_2 =>
      assertion_eq A1_1 A2_1 && assertion_eq A1_2 A2_2
    | AForAll A1, AForAll A2 => assertion_eq A1 A2
    | AApplication A1 t1, AApplication A2 t2 => assertion_eq A1 A2 && (t1 == t2)
    (* Temporal logic *)
    | AAlways' A1, AAlways' A2 => assertion_eq A1 A2
    | AAlwaysP' A1, AAlwaysP' A2 => assertion_eq A1 A2
    | AEventually' A1, AEventually' A2 => assertion_eq A1 A2
    | AEventuallyP' A1, AEventuallyP' A2 => assertion_eq A1 A2
    | ANext A1, ANext A2 => assertion_eq A1 A2
    | APrevious A1, APrevious A2 => assertion_eq A1 A2
    | ASelf A1, ASelf A2 => assertion_eq A1 A2
    (* Unequal *)
    | _, _ => false
    end.

  (* Boolean equality reflection *)
  Lemma assertion_eqP : Equality.axiom assertion_eq.
  Proof.
    elim=>
      [| p1 | A1 IHA | A1_1 IHA1 A1_2 IHA2 | A1 IHA | A1 IHA t1
        | A1 IHA | A1 IHA | A1 IHA | A1 IHA | A1 IHA | A1 IHA | A1 IHA]
      [| p2 | A2 | A2_1 A2_2 | A2 | A2 t2 | A2 | A2 | A2 | A2 | A2 | A2 | A2]
      //=; try by constructor.
    - by have [<- | neqx] := p1 =P p2; last (by right; case); constructor.
    - by have [<- | neqx] := IHA A2; last (by right; case); constructor.
    - have [<- | neqx] := IHA1 A2_1; last (by right; case); simpl.
      have [<- | neqx] := IHA2 A2_2; last (by right; case); simpl.
      by constructor.
    - by have [<- | neqx] := IHA A2; last (by right; case); constructor.
    - have [<- | neqx] := IHA A2; last (by right; case); simpl.
      have [<- | neqx] := t1 =P t2; last (by right; case); simpl.
      by constructor.
    - by have [<- | neqx] := IHA A2; last (by right; case); constructor.
    - by have [<- | neqx] := IHA A2; last (by right; case); constructor.
    - by have [<- | neqx] := IHA A2; last (by right; case); constructor.
    - by have [<- | neqx] := IHA A2; last (by right; case); constructor.
    - by have [<- | neqx] := IHA A2; last (by right; case); constructor.
    - by have [<- | neqx] := IHA A2; last (by right; case); constructor.
    - by have [<- | neqx] := IHA A2; last (by right; case); constructor.
  Qed.

  (* EqType canonical structures *)
  Definition assertion_eqMixin := EqMixin assertion_eqP.
  Canonical assertion_eqType := EqType assertion assertion_eqMixin.

End eq.

(* Constructor coercions *)
Coercion APredicate : predicate >-> assertion.

(* Notation scope *)
Declare Scope assertion_scope.
Bind Scope assertion_scope with assertion.
Delimit Scope assertion_scope with assertion.

Notation "{-A A -}" := (A%assertion)
  (at level 0, A at level 100, no associativity, only parsing).

(* Constructor notations *)
Notation "~ A" := (ANot A) : assertion_scope.
Notation "A1 /\ A2" := (AAnd A1 A2) : assertion_scope.
Notation "forall: A" := (AForAll A)
  (at level 65, A at level 200, right associativity) : assertion_scope.
Notation "A ' t" := (AApplication A t)
  (at level 10, left associativity) : assertion_scope.
Notation "always^ A" := (AAlways' A)
  (at level 60, right associativity) : assertion_scope.
Notation "alwaysp^ A" := (AAlwaysP' A)
  (at level 60, right associativity) : assertion_scope.
Notation "eventually^ A" := (AEventually' A)
  (at level 60, right associativity) : assertion_scope.
Notation "eventuallyp^ A" := (AEventuallyP' A)
  (at level 60, right associativity) : assertion_scope.
Notation "'next' A" := (ANext A)
  (at level 60, right associativity) : assertion_scope.
Notation "'previous' A" := (APrevious A)
  (at level 60, right associativity) : assertion_scope.
Notation "'self' A" := (ASelf A)
  (at level 60, right associativity) : assertion_scope.

(* Constructor notations for predicates *)
Definition AEqual x1 x2 := APredicate (PEqual x1 x2).
Notation "x1 = x2" := (AEqual x1 x2) : assertion_scope.
Definition ALess x1 x2 := APredicate (PLess x1 x2).
Notation "x1 < x2" := (ALess x1 x2) : assertion_scope.
Definition AIn y xs := APredicate (PMember y xs).
Notation "y \in xs" := (AIn y xs) : assertion_scope.
Definition AExtension xs' xs := APredicate (PExtension xs' xs).
Notation "xs' <<< xs" := (AExtension xs' xs)
  (at level 20, no associativity) : assertion_scope.

(* Derived constructor notations for predicate logic *)
Definition ATrue := {-A ~ AFalse -}.
Definition AOr A1 A2 := {-A ~(~A1 /\ ~A2) -}.
Notation "A1 \/ A2" := (AOr A1 A2) : assertion_scope.
Definition AIf A1 A2 := {-A ~A1 \/ A2 -}.
Notation "A1 -> A2" := (AIf A1 A2) : assertion_scope.
Definition AIff A1 A2 := {-A (A1 -> A2) /\ (A2 -> A1) -}.
Notation "A1 <-> A2" := (AIff A1 A2) : assertion_scope.
Definition AExists A := {-A ~forall: ~A -}.
Notation "exists: A" := (AExists A)
  (at level 65, A at level 200, right associativity) : assertion_scope.

(* Derived constructor notations for predicates *)
Definition ANotEqual x1 x2 := {-A ~(x1 = x2) -}.
Notation "x1 <> x2" := (ANotEqual x1 x2) : assertion_scope.
Definition ALessEqual x1 x2 := {-A x1 < x2 \/ x1 = x2 -}.
Notation "x1 <= x2" := (ALessEqual x1 x2) : assertion_scope.
Definition AGreater x1 x2 := {-A ~ x1 <= x2 -}.
Notation "x1 > x2" := (AGreater x1 x2) : assertion_scope.
Definition AGreaterEqual x1 x2 := {-A ~ x1 < x2 -}.
Notation "x1 >= x2" := (ALessEqual x1 x2) : assertion_scope.
Definition ANotIn y xs := {-A ~ y \in xs -}.
Notation "y \notin xs" := (ANotIn y xs) : assertion_scope.

(* Derived strict and immediate past temporal operators *)
Definition APrevious' A := {-A ~previous ~A -}.
Notation "previous^ A" := (APrevious' A)
  (at level 60, right associativity) : assertion_scope.

(* Derived reflexive future temporal operators *)
Definition AEventually A := {-A A \/ eventually^ A -}.
Notation "'eventually' A" := (AEventually A)
  (at level 60, right associativity) : assertion_scope.
Definition AAlways A := {-A A /\ always^ A -}.
Notation "'always' A" := (AAlways A)
  (at level 60, right associativity) : assertion_scope.

(* Derived reflexive past temporal operators *)
Definition AEventuallyP A := {-A A \/ eventuallyp^ A -}.
Notation "'eventuallyp' A" := (AEventuallyP A)
  (at level 60, right associativity) : assertion_scope.
Definition AAlwaysP A := {-A A /\ alwaysp^ A -}.
Notation "'alwaysp' A" := (AAlwaysP A)
  (at level 60, right associativity) : assertion_scope.

(* Additional temporal operators *)
Definition AEntails A1 A2 := {-A always (A1 -> A2) -}.
Notation "A1 =>> A2" := (AEntails A1 A2)
  (at level 99, right associativity) : assertion_scope.
Definition ACongruent A1 A2 := {-A always (A1 <-> A2) -}.
Notation "A1 <=> A2" := (ACongruent A1 A2)
  (at level 95, no associativity) : assertion_scope.
Definition AFollowedBy A1 A2 := {-A A1 =>> eventually A2 -}.
Notation "A1 ~> A2" := (AFollowedBy A1 A2)
  (at level 90, right associativity) : assertion_scope.
Definition APrecededBy A1 A2 := {-A A1 =>> eventuallyp A2 -}.
Notation "A1 <~ A2" := (APrecededBy A1 A2)
  (at level 90, right associativity) : assertion_scope.

(* Component syntactic sugar *)
Definition AOn n A := {-A Fn = n /\ A -}.
Notation "'on' n , A" := (AOn n A)
  (at level 89, right associativity, format "'on'  n ,  A")
  : assertion_scope. (* Between connectives and entailment *)
Definition ATopRequest e :=
  {-A Fd = [] /\ Fo = CRequest /\ Fe = e -}.
Notation "'event' []-> e" := (ATopRequest e)
  (at level 60, no associativity, format "'event' []->  e")
  : assertion_scope.
Definition ATopIndication e :=
  {-A Fd = [] /\ Fo = CIndication /\ Fe = e -}.
Notation "'event' []<- e" := (ATopIndication e)
  (at level 60, no associativity, format "'event' []<-  e")
  : assertion_scope.
Definition ATopPeriodic e :=
  {-A Fd = [] /\ Fo = CPeriodic /\ Fe = e -}.
Notation "'event' []~> e" := (ATopPeriodic e)
  (at level 60, no associativity, format "'event' []~>  e")
  : assertion_scope.
Definition ASubRequest i e :=
  {-A Fd = [i] /\ Fo = CRequest /\ Fe = e -}.
Notation "'event' [ i ]-> e" := (ASubRequest i e)
  (at level 60, no associativity, format "'event' [ i ]->  e")
  : assertion_scope.
Definition ASubIndication i e :=
  {-A Fd = [i] /\ Fo = CIndication /\ Fe = e -}.
Notation "'event' [ i ]<- e" := (ASubIndication i e)
  (at level 60, no associativity, format "'event' [ i ]<-  e")
  : assertion_scope.
Definition ASubPeriodic i e :=
  {-A Fd = [i] /\ Fo = CPeriodic /\ Fe = e -}.
Notation "'event' [ i ]~> e" := (ASubPeriodic i e)
  (at level 60, no associativity, format "'event' [ i ]~>  e")
  : assertion_scope.
Definition ASelfEvent :=
  {-A (exists: Fd = [$0] /\ Fo = CIndication) \/
    (Fd = [] /\ Fo = CRequest) \/
    (Fd = [] /\ Fo = CPeriodic) -}.
Notation "self-event" := ASelfEvent
  (at level 60, no associativity) : assertion_scope.

(* Tactics *)
(* Due to its complexity, folding self-event is most easily accomplished using a
 * lemma establishing the equality of its definition (after explosion and
 * folding) and itself.
 *)
Lemma fold_ASelfEvent :
  AIf
    (AForAll
      (ANot
        (AAnd
          (AEqual Fd (TCons (TParameter (P O O)) TNil))
          (AEqual Fo CIndication))))
    (AOr
      (AAnd (AEqual Fd TNil) (AEqual Fo CRequest))
      (AAnd (AEqual Fd TNil) (AEqual Fo CPeriodic)))
  = ASelfEvent.
Proof. by []. Qed.
Ltac dfold_assertion :=
  dfold_term;
  repeat match goal with
  (* Constructor notations for predicates *)
  | |- context[ APredicate (PEqual ?x1 ?x2) ] => rewrite -/(AEqual x1 x2)
  | |- context[ APredicate (PLess ?x1 ?x2) ] => rewrite -/(ALess x1 x2)
  | |- context[ APredicate (PMember ?y ?xs) ] => rewrite -/(AIn y xs)
  | |- context[ APredicate (PExtension ?xs' ?xs) ] => rewrite -/(AExtension xs' xs)

  (* Derived constructor notations for predicate logic *)
  | |- context[ {-A ~ AFalse -} ] => rewrite -/ATrue
  | |- context[ {-A ~(~?A1 /\ ~?A2) -} ] => rewrite -/(AOr A1 A2)
  | |- context[ {-A ~?A1 \/ ?A2 -} ] => rewrite -/(AIf A1 A2)
  | |- context[ {-A (?A1 -> ?A2) /\ (?A2 -> ?A1) -} ] => rewrite -/(AIff A1 A2)
  | |- context[ {-A ~forall: ~?A -} ] => rewrite -/(AExists A)

  (* Derived constructor notations for predicates *)
  | |- context[ {-A ~(?x1 = ?x2) -} ] => rewrite -/(ANotEqual x1 x2)
  | |- context[ {-A ?x1 < ?x2 \/ ?x1 = ?x2 -} ] => rewrite -/(ALessEqual x1 x2)
  | |- context[ {-A ~ ?x1 <= ?x2 -} ] => rewrite -/(AGreater x1 x2)
  | |- context[ {-A ~ ?x1 < ?x2 -} ] => rewrite -/(AGreaterEqual x1 x2)
  | |- context[ {-A ~ ?y \in ?xs -} ] => rewrite -/(ANotIn y xs)

  (* Derived strict and immediate past temporal operators *)
  | |- context[ {-A ~previous ~?A -} ] => rewrite -/(APrevious' A)

  (* Derived reflexive future temporal operators *)
  | |- context[ {-A ?A \/ eventually^ ?A -} ] => rewrite -/(AEventually A)
  | |- context[ {-A ?A /\ always^ ?A -} ] => rewrite -/(AAlways A)

  (* Derived reflexive past temporal operators *)
  | |- context[ {-A ?A \/ eventuallyp^ ?A -} ] => rewrite -/(AEventuallyP A)
  | |- context[ {-A ?A /\ alwaysp^ ?A -} ] => rewrite -/(AAlwaysP A)

  (* Additional temporal operators *)
  | |- context[ {-A always (?A1 -> ?A2) -} ] => rewrite -/(AEntails A1 A2)
  | |- context[ {-A always (?A1 <-> ?A2) -} ] => rewrite -/(ACongruent A1 A2)
  | |- context[ {-A ?A1 =>> eventually ?A2 -} ] => rewrite -/(AFollowedBy A1 A2)
  | |- context[ {-A ?A1 =>> eventuallyp ?A2 -} ] => rewrite -/(APrecededBy A1 A2)

  (* Component syntactic sugar *)
  | |- context[ {-A TVariable (VF Fn) = ?n /\ ?A -} ] => rewrite -/(AOn n A)
  | |- context[ {-A
    TVariable (VF Fd) = [] /\
    TVariable (VF Fo) = TConstructor CRequest /\
    TVariable (VF Fe) = ?e
  -} ] => rewrite -/(ATopRequest e)
  | |- context[ {-A
    TVariable (VF Fd) = [] /\
    TVariable (VF Fo) = TConstructor CIndication /\
    TVariable (VF Fe) = ?e
  -} ] => rewrite -/(ATopIndication e)
  | |- context[ {-A
    TVariable (VF Fd) = [] /\
    TVariable (VF Fo) = TConstructor CPeriodic /\
    TVariable (VF Fe) = ?e
  -} ] => rewrite -/(ATopPeriodic e)
  | |- context[ {-A
    TVariable (VF Fd) = [?i] /\
    TVariable (VF Fo) = TConstructor CRequest /\
    TVariable (VF Fe) = ?e
  -} ] => rewrite -/(ASubRequest i e)
  | |- context[ {-A
    TVariable (VF Fd) = [?i] /\
    TVariable (VF Fo) = TConstructor CIndication /\
    TVariable (VF Fe) = ?e
  -} ] => rewrite -/(ASubIndication i e)
  | |- context[ {-A
    TVariable (VF Fd) = [?i] /\
    TVariable (VF Fo) = TConstructor CPeriodic /\
    TVariable (VF Fe) = ?e
  -} ] => rewrite -/(ASubPeriodic i e)
  | |- context[ {-A
    (exists: TVariable (VF Fd) = [$0] /\
      TVariable (VF Fo) = TConstructor CIndication) \/
    (TVariable (VF Fd) = [] /\ TVariable (VF Fo) = TConstructor CRequest) \/
    (TVariable (VF Fd) = [] /\ TVariable (VF Fo) = TConstructor CPeriodic)
  -} ] => rewrite -/ASelfEvent
  end;
  rewrite ?fold_ASelfEvent.

(* Forms of non-temporal assertions
 * Non-temporal assertions do not contain any temporal operators.
 *)
Inductive non_temporal_assertion : assertion -> Type :=
| NTAFalse :
  non_temporal_assertion AFalse
| NTAPredicate p :
  non_temporal_assertion (APredicate p)
| NTANot A :
  non_temporal_assertion A ->
  non_temporal_assertion {-A ~A -}
| NTAAnd A1 A2 :
  non_temporal_assertion A1 ->
  non_temporal_assertion A2 ->
  non_temporal_assertion {-A A1 /\ A2 -}
| NTAForAll A :
  non_temporal_assertion A ->
  non_temporal_assertion {-A forall: A -}
| NTAApplication A t :
  non_temporal_assertion A ->
  non_temporal_assertion {-A A ' t -}.

(* Forms of assertions at a particular location
 * Location assertions are restricted to specific forms of atomic assertions
 * and any compositions of those assertions, excluding the next, previous, and
 * self operators.
 *
 * The sequence of naturals represents the distinct location at which the
 * assertion is made.
 *)
Inductive location_assertion : seq nat -> assertion -> Type :=
| LAEventOn d n dp o e :
  location_assertion d {-A on n,
    (Fd = term_of_list [seq term_of_nat i | i <- dp ++ d] /\
      Fo = o /\ Fe = e) -}
| LACorrect d n :
  location_assertion d {-A n \in UCorrect -}
| LANot d A :
  location_assertion d A ->
  location_assertion d {-A ~A -}
| LAAnd d A1 A2 :
  location_assertion d A1 ->
  location_assertion d A2 ->
  location_assertion d {-A A1 /\ A2 -}
| LAForAll d A :
  location_assertion d A ->
  location_assertion d {-A forall: A -}
| LAApplication d A t :
  location_assertion d A ->
  location_assertion d {-A A ' t -}
| LAAlways' d A :
  location_assertion d A ->
  location_assertion d {-A always^ A -}
| LAAlwaysP' d A :
  location_assertion d A ->
  location_assertion d {-A alwaysp^ A -}
| LAEventually' d A :
  location_assertion d A ->
  location_assertion d {-A eventually^ A -}
| LAEventuallyP' d A :
  location_assertion d A ->
  location_assertion d {-A eventuallyp^ A -}.

(* Derived first-order operators *)
Lemma LAOr d A1 A2 :
  location_assertion d A1 ->
  location_assertion d A2 ->
  location_assertion d {-A A1 \/ A2 -}.
Proof. move=> LA1 LA2; by repeat constructor. Defined.
Hint Resolve LAOr : core.

Lemma LAIf d A1 A2 :
  location_assertion d A1 ->
  location_assertion d A2 ->
  location_assertion d {-A A1 -> A2 -}.
Proof. move=> LA1 LA2; by repeat constructor. Defined.
Hint Resolve LAIf : core.

Lemma LAIff d A1 A2 :
  location_assertion d A1 ->
  location_assertion d A2 ->
  location_assertion d {-A A1 <-> A2 -}.
Proof. move=> LA1 LA2; by repeat constructor. Defined.
Hint Resolve LAIff : core.

Lemma LAExists d A :
  location_assertion d A ->
  location_assertion d {-A exists: A -}.
Proof. move=> LA; by repeat constructor. Defined.
Hint Resolve LAExists : core.

(* Derived reflexive future temporal operators *)
Lemma LAEventually d A :
  location_assertion d A ->
  location_assertion d {-A eventually A -}.
Proof. move=> LA; by repeat constructor. Defined.
Hint Resolve LAEventually : core.

Lemma LAAlways d A :
  location_assertion d A ->
  location_assertion d {-A always A -}.
Proof. move=> LA; by repeat constructor. Defined.
Hint Resolve LAAlways : core.

(* Derived reflexive past temporal operators *)
Lemma LAEventuallyP d A :
  location_assertion d A ->
  location_assertion d {-A eventuallyp A -}.
Proof. move=> LA; by repeat constructor. Defined.
Hint Resolve LAEventuallyP : core.

Lemma LAAlwaysP d A :
  location_assertion d A ->
  location_assertion d {-A alwaysp A -}.
Proof. move=> LA; by repeat constructor. Defined.
Hint Resolve LAAlwaysP : core.

(* Additional temporal operators *)
Lemma LAEntails d A1 A2 :
  location_assertion d A1 ->
  location_assertion d A2 ->
  location_assertion d {-A A1 =>> A2 -}.
Proof. move=> LA1 LA2; by repeat constructor. Defined.
Hint Resolve LAEntails : core.

Lemma LACongruent d A1 A2 :
  location_assertion d A1 ->
  location_assertion d A2 ->
  location_assertion d {-A A1 <=> A2 -}.
Proof. move=> LA1 LA2; by repeat constructor. Defined.
Hint Resolve LACongruent : core.

Lemma LAFollowedBy d A1 A2 :
  location_assertion d A1 ->
  location_assertion d A2 ->
  location_assertion d {-A A1 ~> A2 -}.
Proof. move=> LA1 LA2; by repeat constructor. Defined.
Hint Resolve LAFollowedBy : core.

Lemma LAPrecededBy d A1 A2 :
  location_assertion d A1 ->
  location_assertion d A2 ->
  location_assertion d {-A A1 <~ A2 -}.
Proof. move=> LA1 LA2; by repeat constructor. Defined.
Hint Resolve LAPrecededBy : core.

(* Forms of assertions on the top component
 * Top assertions are simply location assertions specialized for the empty
 * distinct location.
 *)
Definition top_assertion := location_assertion [::].

(* Forms of assertions that are invariants at a particular location
 * Location invariants are location assertions in which the outermost operator
 * is the always-in-the-future operator.
 *)
Inductive location_invariant : seq nat -> assertion -> Type :=
| LIA d A :
  location_assertion d A ->
  location_invariant d {-A always A -}.

(* Every location invariant is also a location assertion *)
Lemma location_invariant_assertion d A :
  location_invariant d A ->
  location_assertion d A.
Proof.
  by case=> ???; apply: LAAlways.
Defined.

(* Forms of assertions that are invariants on the top component
 * Top invariants are simply location invariants specialized for the empty
 * distinct location.
 *)
Definition top_invariant := location_invariant [::].

(* Forms of assertions that are self invariants
 * Self invariants are restricted to specific forms of atomic assertions and
 * any compositions of those assertions, excluding the next, previous, and
 * self operators.
 *
 * The sequence of naturals represents the distinct location at which the
 * assertion is made.
 *)
Inductive self_invariant : assertion -> Type :=
| SITopRequestOn n e :
  self_invariant {-A on n, event []-> e -}
| SITopPeriodicOn n e :
  self_invariant {-A on n, event []~> e -}
| SISubIndicationOn n i e :
  self_invariant {-A on n, event [i]<- e -}
| SICorrect n :
  self_invariant {-A n \in UCorrect -}
| SINot A :
  self_invariant A ->
  self_invariant {-A ~A -}
| SIAnd A1 A2 :
  self_invariant A1 ->
  self_invariant A2 ->
  self_invariant {-A A1 /\ A2 -}
| SIForAll A :
  self_invariant A ->
  self_invariant {-A forall: A -}
| SIApplication A t :
  self_invariant A ->
  self_invariant {-A A ' t -}
| SIAlways' A :
  self_invariant A ->
  self_invariant {-A always^ A -}
| SIAlwaysP' A :
  self_invariant A ->
  self_invariant {-A alwaysp^ A -}
| SIEventually' A :
  self_invariant A ->
  self_invariant {-A eventually^ A -}
| SIEventuallyP' A :
  self_invariant A ->
  self_invariant {-A eventuallyp^ A -}.

(* Forms of assertions that are rigid predicates *)
Inductive rigid_predicate : assertion -> Type :=
| RPEqual x1 x2 :
  rigid_predicate {-A x1 = x2 -}.
