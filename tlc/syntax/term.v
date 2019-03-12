(* TLC in Coq
 *
 * Module: tlc.syntax.term
 * Purpose: Contains the syntax of terms.
 *)

Require Import mathcomp.ssreflect.eqtype.
Require Import mathcomp.ssreflect.seq.
Require Import mathcomp.ssreflect.ssrbool.
Require Import mathcomp.ssreflect.ssreflect.
Require Import mathcomp.ssreflect.ssrnat.
Require Import tlc.syntax.constructor.
Require Import tlc.syntax.function.
Require Import tlc.syntax.literal.
Require Import tlc.syntax.parameter.
Require Import tlc.syntax.pattern.
Require Import tlc.syntax.variable.
Require Import tlc.utility.functor.
Require Import tlc.utility.set.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Forms of computational terms *)
Inductive term :=
| TFailure (* Computation error *)
| TParameter (p : parameter) (* Nameless bound parameters *)
| TVariable (v : variable) (* Named free variables *)
| TConstructor (c : constructor) (* Value constructors *)
| TLiteral (l : literal) (* Value literals *)
| TFunction (f : function) (* External functions *)
| TApplication (tf ta : term) (* Function application *)
| TAbstraction (tb : term) (* Function abstraction *)
| TMatch (ta : term) (cs : cases) (* Pattern matching *)
(* Cases of pattern matching *)
with case :=
| TCase (p : pattern) (t : term)
with cases :=
| TCNil
| TCCons (c : case) (cs : cases).

(* Equality *)
Section eq.

  (* Boolean equality
   * As a consequence of the locally nameless representation, syntactic
   * equality is equivalent to equality under alpha-conversion.
   *)
  Fixpoint term_eq tl tr :=
    match tl, tr with
    | TFailure, TFailure => true
    | TFailure, _ => false
    | TParameter pl, TParameter pr => pl == pr
    | TParameter _, _ => false
    | TVariable vl, TVariable vr => vl == vr
    | TVariable _, _ => false
    | TConstructor cl, TConstructor cr => cl == cr
    | TConstructor _, _ => false
    | TLiteral ll, TLiteral lr => ll == lr
    | TLiteral _, _ => false
    | TFunction fl, TFunction fr => fl == fr
    | TFunction _, _ => false
    | TApplication tfl tal, TApplication tfr tar =>
      term_eq tfl tfr && term_eq tal tar
    | TApplication _ _, _ => false
    | TAbstraction tbl, TAbstraction tbr => term_eq tbl tbr
    | TAbstraction _, _ => false
    | TMatch tal csl, TMatch tar csr =>
      term_eq tal tar && cases_eq csl csr
    | TMatch _ _, _ => false
    end
  with case_eq cl cr :=
    match cl, cr with
    | TCase pl tl, TCase pr tr => (pl == pr) && term_eq tl tr
    end
  with cases_eq csl csr :=
    match csl, csr with
    | TCNil, TCNil => true
    | TCNil, _ => false
    | TCCons cl csl, TCCons cr csr => case_eq cl cr && cases_eq csl csr
    | TCCons _ _, _ => false
    end.

  (* Boolean equality reflection *)
  Fixpoint term_eqP tl tr : reflect (tl = tr) (term_eq tl tr)
  with case_eqP cl cr : reflect (cl = cr) (case_eq cl cr)
  with cases_eqP csl csr : reflect (csl = csr) (cases_eq csl csr).
  Proof.
    (* term_eqP *)
    elim: tl tr => [| pl | vl | cl | ll | fl | tfl IHtf tal IHta | tbl IHtb |
      tal IHta csl] [| pr | vr | cr | lr | fr | tfr tar | tbr | tar csr] //=;
      try by constructor.
    - case H: (pl == pr); move/eqP: H => H //=; subst;
        last by constructor; move=> [].
      by constructor.
    - case H: (vl == vr); move/eqP: H => H //=; subst;
        last by constructor; move=> [].
      by constructor.
    - case H: (cl == cr); move/eqP: H => H //=; subst;
        last by constructor; move=> [].
      by constructor.
    - case H: (ll == lr); move/eqP: H => H //=; subst;
        last by constructor; move=> [].
      by constructor.
    - case H: (fl == fr); move/eqP: H => H //=; subst;
        last by constructor; move=> [].
      by constructor.
    - case H: (term_eq tfl tfr); move/IHtf: H => H //=; subst;
        last by constructor; move=> [].
      case H: (term_eq tal tar); move/IHta: H => H //=; subst;
        last by constructor; move=> [].
      by constructor.
    - case H: (term_eq tbl tbr); move/IHtb: H => H //=; subst;
        last by constructor; move=> [].
      by constructor.
    - case H: (term_eq tal tar); move/IHta: H => H //=; subst;
        last by constructor; move=> [].
      case H: (cases_eq csl csr); move/cases_eqP: H => H //=; subst;
        last by constructor; move=> [].
      by constructor.

    (* case_eqP *)
    elim: cl cr => [pl tl] [pr tr] //=; try by constructor.
    case H: (pl == pr); move/eqP: H => H //=; subst;
      last by constructor; move=> [].
    case H: (term_eq tl tr); move/term_eqP: H => H //=; subst;
      last by constructor; move=> [].
    by constructor.

    (* cases_eqP *)
    elim: csl csr => [| cl csl IHcs] [| cr csr] //=; try by constructor.
    case H: (case_eq cl cr); move/case_eqP: H => H //=; subst;
      last by constructor; move=> [].
    case H: (cases_eq csl csr); move/IHcs: H => H //=; subst;
      last by constructor; move=> [].
    by constructor.
  Qed.

  (* EqType canonical structures *)
  Canonical Structure term_eqMixin :=
    Eval hnf in EqMixin term_eqP.
  Canonical Structure term_eqType :=
    Eval hnf in EqType term term_eqMixin.
  Canonical Structure case_eqMixin :=
    Eval hnf in EqMixin case_eqP.
  Canonical Structure case_eqType :=
    Eval hnf in EqType case case_eqMixin.
  Canonical Structure cases_eqMixin :=
    Eval hnf in EqMixin cases_eqP.
  Canonical Structure cases_eqType :=
    Eval hnf in EqType cases cases_eqMixin.

End eq.

(* Constructor coercions *)
Coercion TParameter : parameter >-> term.
Coercion TVariable : variable >-> term.
Coercion TConstructor : constructor >-> term.
Coercion TLiteral : literal >-> term.
Coercion TFunction : function >-> term.

(* Notation scope *)
Bind Scope term_scope with term.
Delimit Scope term_scope with term.
Notation "{t: t }" := (t%term)
  (at level 0, t at level 100, no associativity, only parsing).
Bind Scope case_scope with case.
Delimit Scope case_scope with case.
Notation "{c: c }" := (c%case)
  (at level 0, c at level 100, no associativity, only parsing).
Bind Scope cases_scope with cases.
Delimit Scope cases_scope with cases.
Notation "{cs: cs }" := (cs%cases)
  (at level 0, cs at level 100, no associativity, only parsing).

(* Constructor notations *)
Notation "# j" := (TParameter (P 0 j))
  (at level 0, no associativity, format "'#' j") : term_scope.
Notation "#( i , j )" := (TParameter (P i j))
  (at level 0, no associativity, format "'#(' i ','  j ')'") : term_scope.
Notation "tf $ ta" := (TApplication tf ta)
  (at level 10, left associativity) : term_scope.
Notation "fun: tb" := (TAbstraction tb)
  (at level 20, right associativity, tb at level 100) : term_scope.
Notation "match: ta with: csl 'endmatch'" := (TMatch ta csl)
  (at level 20, right associativity, ta at level 100, csl at level 0)
  : term_scope.
Notation "p -> t" := (TCase p t) : case_scope.
Notation "[ ]" := (TCNil) : cases_scope.
Notation "{{ c1 | .. | cn }}" := (TCCons c1 (.. (TCCons cn TCNil) ..))
  : cases_scope.

(* Derived constructor notations *)
Definition TLet p ta tm := {t: match: ta with: {{ p -> tm }} endmatch}.
Notation "let: p := ta in: tm" := (TLet p ta tm)
  (at level 20, right associativity, ta at level 100, tm at level 100)
  : term_scope.
Definition TIf ta ti te := {t:
  match: ta with:
  {{ true -> ti
   | false -> te
  }} endmatch
}.
Notation "if: ta then: ti else: te" := (TIf ta ti te)
  (at level 20, right associativity, ta at level 100, ti at level 100,
    te at level 100) : term_scope.

(* Pair constructor notations *)
Definition TPair tl tr := {t: CPair $ tl $ tr}.
Notation "( t1 , t2 , .. , tn )" :=
  {t: TPair (.. (TPair t1 t2) ..) tn} : term_scope.

(* List constructor notations *)
Definition TNil := TConstructor CNil.
Notation "[ ]" := TNil : term_scope.
Definition TCons t ts := {t: CCons $ t $ ts}.
Notation "t :: ts" := (TCons t ts) : term_scope.
Notation "[ t1 , .. , tn ]" := {t: t1 :: (.. (tn :: []) ..)}
  : term_scope.

(* Function notations *)
(* Generic *)
Definition TEqual tl tr := {t: FEqual $ tl $ tr}.
Notation "tl = tr" := (TEqual tl tr) : term_scope.
(* Boolean *)
Definition TNot t := {t: FNot $ t}.
Notation "~ t" := (TNot t) : term_scope.
Definition TOr tl tr := {t: FOr $ tl $ tr}.
Notation "tl \/ tr" := (TOr tl tr) : term_scope.
(* Natural *)
Definition TSucc t := {t: FSucc $ t}.
Notation "t .+1" := (TSucc t) : term_scope.
Definition TAdd tl tr := {t: FAdd $ tl $ tr}.
Notation "tl + tr" := (TAdd tl tr) : term_scope.
(* List *)
Definition TConcat tsl tsr := {t: FConcat $ tsl $ tsr}.
Notation "tsl ++ tsr" := (TConcat tsl tsr) : term_scope.
Definition TUnion tsl tsr := {t: FUnion $ tsl $ tsr}.
Notation "tsl \union tsr" := (TUnion tsl tsr) : term_scope.
Definition TMap tf ts := {t: FMap $ tf $ ts}.
Notation "tf <$> ts" := (TMap tf ts) : term_scope.

(* List conversion *)
Fixpoint TList ts :=
  match ts with
  | [::] => {t: []}
  | t :: ts => {t: t :: TList ts}
  end.

(* Derived generic functions *)
Definition FNotEqual := {t: fun: fun: ~(#(1, 0) = #0)}.
Definition TNotEqual tl tr := {t: FNotEqual $ tl $ tr}.
Notation "tl <> tr" := (TNotEqual tl tr) : term_scope.

(* Derived Boolean functions *)
Definition FAnd := {t: fun: fun: ~(~#(1, 0) \/ ~#0)}.
Definition TAnd tl tr := {t: FAnd $ tl $ tr}.
Notation "tl /\ tr" := (TAnd tl tr) : term_scope.

(* Derived list functions *)
Definition FMember := {t: fun: fun: (FCount $ #(1, 0) $ #0) <> 0}.
Definition TMember t ts := {t: FMember $ t $ ts}.
Notation "t \in ts" := (TMember t ts) : term_scope.

(* Derived predicates *)
Definition FCorrect := {t: fun: #0 \in "Correct"}.
Definition TCorrect tn := {t: FCorrect $ tn}.
