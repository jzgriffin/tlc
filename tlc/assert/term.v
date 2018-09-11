From mathcomp.ssreflect
Require Import ssreflect eqtype ssrbool seq.

Require Import variable constant function.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Inductive term : Type :=
| Tvar : variable -> term
| Tconst : constant -> term
| Tfunc : function -> seq term -> term.

(* Equality *)
Section term_eq.

  Fixpoint eq_term (t t' : term) :=
    (* TODO: Re-evaluate this approach *)
    let eq_terms := fix eq_terms ts ts' :=
      match ts, ts' with
      | [::], [::] => true
      | t :: h, t' :: h' => eq_term t t' && eq_terms h h'
      | _, _ => false
      end in
    match t, t' with
    | Tvar x, Tvar x' => x == x'
    | Tvar _, _ => false
    | Tconst c, Tconst c' => c == c'
    | Tconst _, _ => false
    | Tfunc f ts, Tfunc f' ts' => (f == f') && eq_terms ts ts'
    | Tfunc _ _, _ => false
    end.

  Lemma eq_termP : Equality.axiom eq_term.
  Proof.
    (* TODO *)
  Admitted.

  Canonical term_eqMixin :=
    Eval hnf in EqMixin eq_termP.
  Canonical term_eqType :=
    Eval hnf in EqType term term_eqMixin.

End term_eq.

(* Coercions *)
Coercion Tvar : variable >-> term.
Coercion Tconst : constant >-> term.

Fixpoint term_seq (ts : seq term) : term :=
  match ts with
  | [::] => Cnil
  | h :: ts' => Tfunc Fcons [:: h; term_seq ts']
  end.

Fixpoint seq_term (t : term) : seq term :=
  match t with
  | Tfunc Fcons [:: h; t'] => h :: seq_term t'
  | _ => [::] (* Including Cnil *)
  end.

(* Operations *)
Section term_op.

  Fixpoint term_free_vars t :=
    match t with
    | Tvar x => [:: x]
    | Tconst _ => [::]
    | Tfunc _ ts => flatten [seq term_free_vars t' | t' <- ts]
    end.

  Definition term_transformer := variable -> option term.

  Fixpoint term_subst tr t :=
    match t with
    | Tvar x => if tr x is Some t' then t' else t
    | Tconst _ => t
    | Tfunc f ts => Tfunc f [seq term_subst tr t' | t' <- ts]
    end.

End term_op.
