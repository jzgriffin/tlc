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
| TFailure
| TParameter (p : parameter)
| TVariable (v : variable)
| TConstructor (c : constructor)
| TLiteral (l : literal)
| TFunction (f : function)
| TApplication (tf ta : term)
| TAbstraction (tb : term)
| TMatch (p : pattern) (ta tm tf : term).

(* Equality *)
Section eq.

  (* Boolean equality
   * As a consequence of the locally nameless representation, syntactic
   * equality is equivalent to equality under alpha-conversion *)
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
    | TMatch pl tal tml tfl, TMatch pr tar tmr tfr =>
      (pl == pr) && term_eq tal tar && term_eq tml tmr && term_eq tfl tfr
    | TMatch _ _ _ _, _ => false
    end.

  (* Boolean equality reflection *)
  Lemma term_eqP : Equality.axiom term_eq.
  Proof.
    elim=> [| pl | vl | cl | ll | fl | tfl IHtf tal IHta | tbl IHtb |
      pl tal IHta tml IHtm tfl IHtf] [| pr | vr | cr | lr | fr | tfr tar |
      tbr | pr tar tmr tfr]
      //=; try by constructor.
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
    - case H: (pl == pr); move/eqP: H => H //=; subst;
        last by constructor; move=> [].
      case H: (term_eq tal tar); move/IHta: H => H //=; subst;
        last by constructor; move=> [].
      case H: (term_eq tml tmr); move/IHtm: H => H //=; subst;
        last by constructor; move=> [].
      case H: (term_eq tfl tfr); move/IHtf: H => H //=; subst;
        last by constructor; move=> [].
      by constructor.
  Qed.

  (* EqType canonical structures *)
  Canonical Structure term_eqMixin := EqMixin term_eqP.
  Canonical Structure term_eqType :=
    Eval hnf in EqType term term_eqMixin.

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

(* Constructor notations *)
Notation "# j" := (TParameter (P 0 j))
  (at level 0, no associativity, format "'#' j") : term_scope.
Notation "#( i , j )" := (TParameter (P i j))
  (at level 0, no associativity, format "'#(' i ','  j ')'") : term_scope.
Notation "tf $ ta" := (TApplication tf ta)
  (at level 10, left associativity) : term_scope.
Notation "fun: tb" := (TAbstraction tb)
  (at level 20, right associativity, tb at level 100) : term_scope.
Notation "match: ta with: p then: tm else: tf" := (TMatch p ta tm tf)
  (at level 20, right associativity, ta at level 100, tm at level 100,
    tf at level 100) : term_scope.

(* Derived constructor notations *)
Definition TLet p ta tm := {t: match: ta with: p then: tm else: TFailure}.
Notation "let: p := ta in: tm" := (TLet p ta tm)
  (at level 20, right associativity, ta at level 100, tm at level 100)
  : term_scope.
Definition TIf ta ti te := {t:
  match: ta with: true then: ti else:
  match: ta with: false then: te else: TFailure}.
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
