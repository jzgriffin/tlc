From mathcomp.ssreflect
Require Import ssreflect eqtype ssrbool seq.
From tlc.utility
Require Import seq.

Require Import variable constant function term predicate.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Inductive assertion : Type :=
| Afalse : assertion (* Empty assertion *)
| Apred : predicate -> seq term -> assertion (* Predicate application *)
| Aconj : assertion -> assertion -> assertion (* Cojunction *)
| Aneg : assertion -> assertion (* Negation *)
| Auniv : variable -> assertion -> assertion (* Universal quantification *)
| Aalwaysfs : assertion -> assertion (* Always strictly in the future *)
| Aalwaysps : assertion -> assertion (* Always strictly in the past *)
| Aeventfs : assertion -> assertion (* Eventually strictly in the future *)
| Aeventps : assertion -> assertion (* Eventually strictly in the past *)
| Anext : assertion -> assertion (* In the next event *)
| Aself : assertion -> assertion.

(* Equality *)
Section assertion_eq.

  Fixpoint eq_assertion (A A' : assertion) :=
    match A, A' with
    | Afalse, Afalse => true
    | Afalse, _ => false
    | Apred p ts, Apred p' ts' => (p == p') && (ts == ts')
    | Apred _ _, _ => false
    | Aconj A1 A2, Aconj A1' A2' => eq_assertion A1 A1' && eq_assertion A2 A2'
    | Aconj _ _, _ => false
    | Aneg A0, Aneg A0' => eq_assertion A0 A0'
    | Aneg _, _ => false
    | Auniv x A0, Auniv x' A0' => (x == x') && eq_assertion A0 A0'
    | Auniv _ _, _ => false
    | Aalwaysfs A0, Aalwaysfs A0' => eq_assertion A0 A0'
    | Aalwaysfs _, _ => false
    | Aalwaysps A0, Aalwaysfs A0' => eq_assertion A0 A0'
    | Aalwaysps _, _ => false
    | Aeventfs A0, Aeventfs A0' => eq_assertion A0 A0'
    | Aeventfs _, _ => false
    | Aeventps A0, Aeventfs A0' => eq_assertion A0 A0'
    | Aeventps _, _ => false
    | Anext A0, Anext A0' => eq_assertion A0 A0'
    | Anext _, _ => false
    | Aself A0, Aalwaysfs A0' => eq_assertion A0 A0'
    | Aself _, _ => false
    end.

  Lemma eq_assertionP : Equality.axiom eq_assertion.
  Proof.
    (* TODO *)
  Admitted.

  Canonical assertion_eqMixin :=
    Eval hnf in EqMixin eq_assertionP.
  Canonical assertion_eqType :=
    Eval hnf in EqType assertion assertion_eqMixin.

End assertion_eq.

(* Syntactic sugars *)
Definition Atrue := (* Unit assertion *)
  Aneg Afalse.
Definition Aeq t1 t2 := (* Equality *)
  Apred Peq [:: t1; t2].
Definition Adisj A1 A2 := (* Disjunction *)
  Aneg (Aconj (Aneg A1) (Aneg A2)).
Definition Aimpl A1 A2 := (* Implication *)
  Adisj (Aneg A1) A2.
Definition Abicond A1 A2 := (* Bicondition *)
  Aconj (Aimpl A1 A2) (Aimpl A2 A1).
Definition Aexis x A := (* Existential quantification *)
  Aneg (Auniv x (Aneg A)).
Definition Aalwaysf A := (* Always in the future *)
  Adisj A (Aalwaysfs A).
Definition Aalwaysp A := (* Always in the past *)
  Adisj A (Aalwaysps A).
Definition Aeventf A := (* Eventually in the future *)
  Adisj A (Aeventfs A).
Definition Aeventp A := (* Eventually in the past *)
  Adisj A (Aeventps A).
Definition Aon n A := (* On node n *)
  Aconj (Aeq Vfn n) A.
Definition Aev d o e := (* Event e at d with orientation o *)
  Aconj (Aeq Vfd d) (Aconj (Aeq Vfo o) (Aeq Vfe e)).
Definition Astrongimpl A1 A2 := (* Strong implication *)
  Aimpl (Aalwaysf A1) A2.
Definition Aleadto A1 A2 := (* A1 leads to A2 *)
  Aimpl (Aalwaysf A1) (Aeventf A2).
Definition Aprecby A1 A2 := (* A1 is preceded by A2 *)
  Aimpl (Aalwaysf A1) (Aeventp A2).

(* Operations *)
Section assertion_op.

  Fixpoint free_vars A :=
    match A with
    | Afalse => [::]
    | Apred p ts => undup (flatten [seq term_free_vars t | t <- ts])
    | Aconj A1 A2 => (free_vars A1) <+> (free_vars A2)
    | Aneg A0 => free_vars A0
    | Auniv x A0 => rem x (free_vars A0)
    | Aalwaysfs A0 => free_vars A0
    | Aalwaysps A0 => free_vars A0
    | Aeventfs A0 => free_vars A0
    | Aeventps A0 => free_vars A0
    | Anext A0 => free_vars A0
    | Aself A0 => free_vars A0
    end.

  Definition free_var x A := x \in free_vars A.

  Fixpoint vars A :=
    match A with
    | Afalse => [::]
    | Apred p ts => free_vars A
    | Aconj A1 A2 => (vars A1) <+> (vars A2)
    | Aneg A0 => vars A0
    | Auniv x A0 => x :: free_vars A0
    | Aalwaysfs A0 => vars A0
    | Aalwaysps A0 => vars A0
    | Aeventfs A0 => vars A0
    | Aeventps A0 => vars A0
    | Anext A0 => vars A0
    | Aself A0 => vars A0
    end.

  Definition generalize A :=
    foldr Auniv A (free_vars A).

  Fixpoint subst tr A :=
    let univ_subst x A :=
      let tr' x' := fun v => if v == x then Some (Tvar x') else tr v in
      let x' :=
        let p y :=
          x \in term_free_vars (if tr y is Some y' then y' else Tvar y) in
        if has p (rem x (free_vars A)) then
          fresh_var x (free_vars (subst (tr' x) A))
        else x in
      Auniv x' (subst (tr' x') A)
    in
    match A with
    | Afalse => Afalse
    | Apred p ts => Apred p [seq term_subst tr t | t <- ts]
    | Aconj A1 A2 => Aconj (subst tr A1) (subst tr A2)
    | Aneg A0 => Aneg (subst tr A0)
    | Auniv x A0 => univ_subst x A0
    | Aalwaysfs A0 => Aalwaysfs (subst tr A0)
    | Aalwaysps A0 => Aalwaysps (subst tr A0)
    | Aeventfs A0 => Aeventfs (subst tr A0)
    | Aeventps A0 => Aeventps (subst tr A0)
    | Anext A0 => Anext (subst tr A0)
    | Aself A0 => Aself (subst tr A0)
    end.

  Definition var_subst x t A :=
    let tr y := if y == x then Some t else None in
    subst tr A.

End assertion_op.
