From mathcomp.ssreflect
Require Import ssreflect eqtype ssrbool seq.

Require Import variable constant function term predicate assertion.

Bind Scope assert_scope with assertion.
Delimit Scope assert_scope with A.

Module AssertNotations.

(* Terms *)

Notation "f // ts" :=
  (Tfunc f ts)
  (at level 95, no associativity) : assert_scope.
Notation "f /()" :=
  (Tfunc f nil)
  (at level 95, no associativity) : assert_scope.
Notation "f /( x , .. , y )" :=
  (Tfunc f (@cons term x (.. (@cons term y nil) .. )))
  (at level 95, no associativity) : assert_scope.

Notation "[]" :=
  Cnil
  (at level 0) : assert_scope.
Notation "[ x ]" :=
  (Fcons/(x, Cnil))%A
  (no associativity) : assert_scope.
Notation "[ x ; .. ; y ]" :=
  (Fcons/(x, (.. (Fcons/(y, Cnil)) .. )))%A
  (no associativity) : assert_scope.

(* Assertions *)

Notation "p /? ts" :=
  (Apred p ts)
  (at level 95, no associativity) : assert_scope.
Notation "p ?()" :=
  (Apred p nil)
  (at level 95, no associativity) : assert_scope.
Notation "p ?( x , .. , y )" :=
  (Apred p (@cons term x (.. (@cons term y nil) .. )))
  (at level 95, no associativity) : assert_scope.

Notation "A /\ B" :=
  (Aconj A B)
  (at level 80, right associativity) : assert_scope.
Notation "~ A" :=
  (Aneg A)
  (at level 75, right associativity) : assert_scope.
Notation "'univ:' x , A" :=
  (Auniv x A)
  (at level 65, right associativity) : assert_scope.
Notation "'alwaysf^:' A" :=
  (Aalwaysfs A)
  (at level 65, right associativity) : assert_scope.
Notation "'alwaysp^:' A" :=
  (Aalwaysps A)
  (at level 65, right associativity) : assert_scope.
Notation "'eventf^:' A" :=
  (Aeventfs A)
  (at level 65, right associativity) : assert_scope.
Notation "'eventp^:' A" :=
  (Aeventps A)
  (at level 65, right associativity) : assert_scope.
Notation "'next:' A" :=
  (Anext A)
  (at level 65, right associativity) : assert_scope.
Notation "'self:' A" :=
  (Aself A)
  (at level 65, right associativity) : assert_scope.

(* Syntactic sugars *)

Notation "x = y" :=
  (Aeq x y)
  (at level 70, no associativity) : assert_scope.
Notation "A \/ B" :=
  (Adisj A B)
  (at level 85, right associativity) : assert_scope.
Notation "A -> B" :=
  (Aimpl A B)
  (at level 99, right associativity, B at level 200) : assert_scope.
Notation "A <-> B" :=
  (Abicond A B)
  (at level 95, no associativity) : assert_scope.
Notation "'exis:' x , A" :=
  (Aexis x A)
  (at level 65, right associativity) : assert_scope.
Notation "'alwaysf:' A" :=
  (Aalwaysf A)
  (at level 65, right associativity) : assert_scope.
Notation "'alwaysp:' A" :=
  (Aalwaysp A)
  (at level 65, right associativity) : assert_scope.
Notation "'eventf:' A" :=
  (Aeventf A)
  (at level 65, right associativity) : assert_scope.
Notation "'eventp:' A" :=
  (Aeventp A)
  (at level 65, right associativity) : assert_scope.
Notation "'on:' n , A" :=
  (Aon n A)
  (at level 65, right associativity) : assert_scope.
Notation "'ev:' d , o , e" :=
  (Aev d o e)
  (at level 65, right associativity) : assert_scope.
Notation self_ev :=
  ((Vfd = [] /\ Vro = Creq_ev) \/
   (Vfd = [] /\ Vro = Cper_ev) \/
   (univ: Vri, (Vfd = [Vri] /\ Vro = Cind_ev)))%A.
Notation "A => B" :=
  (Astrongimpl A B)
  (at level 98, right associativity) : assert_scope.
Notation "A ~> B" :=
  (Aleadto A B)
  (at level 97, right associativity) : assert_scope.
Notation "A <~ B" :=
  (Aprecby A B)
  (at level 97, right associativity) : assert_scope.

End AssertNotations.
