(* TLC in Coq
 *
 * Module: tlc.syntax.term
 * Purpose: Contains the syntax of terms.
 *)

Require Import mathcomp.ssreflect.eqtype.
Require Import mathcomp.ssreflect.seq.
Require Import mathcomp.ssreflect.ssrbool.
Require Import mathcomp.ssreflect.ssreflect.
Require Import mathcomp.ssreflect.ssrfun.
Require Import mathcomp.ssreflect.ssrnat.
Require Import tlc.syntax.constructor.
Require Import tlc.syntax.flexible.
Require Import tlc.syntax.function.
Require Import tlc.syntax.parameter.
Require Import tlc.syntax.pattern.
Require Import tlc.syntax.unknown.
Require Import tlc.syntax.variable.
Require Import tlc.utility.functor.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Forms of computational terms *)
Inductive term :=
| TParameter (x : parameter)
| TVariable (x : variable)
| TConstructor (c : constructor)
| TFunction (f : function)
| TUnknown (u : unknown)
| TApplication (f a : term)
| TMatch (cs : seq (pattern * term)).
Definition match_case := prod pattern term.
Definition match_cases := seq match_case.

(* Equality *)
Section eq.

  (* Boolean equality *)
  Fixpoint term_eq t1 t2 :=
    let fix cases_eq cs1 cs2 :=
      match cs1, cs2 with
      | [::], [::] => true
      | (p1, t1) :: cs1, (p2, t2) :: cs2 => (p1 == p2) && term_eq t1 t2 && cases_eq cs1 cs2
      | _, _ => false
      end in
    match t1, t2 with
    | TParameter x1, TParameter x2 => x1 == x2
    | TVariable x1, TVariable x2 => x1 == x2
    | TConstructor c1, TConstructor c2 => c1 == c2
    | TFunction f1, TFunction f2 => f1 == f2
    | TUnknown u1, TUnknown u2 => u1 == u2
    | TApplication f1 a1, TApplication f2 a2 => term_eq f1 f2 && term_eq a1 a2
    | TMatch cs1, TMatch cs2 => cases_eq cs1 cs2
    | _, _ => false
    end.

  (* Boolean equality reflection *)
  Fixpoint term_eqP t1 t2 : reflect (t1 = t2) (term_eq t1 t2).
  Proof.
    move: t1 t2; case=> [x1 |x1 | c1 | f1 | u1 | f1 a1 | cs1]
      [x2 | x2 | c2 | f2 | u2 | f2 a2 | cs2] //=; try by constructor.
    - by have [<- | neqx] := x1 =P x2; last (by right; case); constructor.
    - by have [<- | neqx] := x1 =P x2; last (by right; case); constructor.
    - by have [<- | neqx] := c1 =P c2; last (by right; case); constructor.
    - by have [<- | neqx] := f1 =P f2; last (by right; case); constructor.
    - by have [<- | neqx] := u1 =P u2; last (by right; case); constructor.
    - have [<- | neqx] := term_eqP f1 f2; last (by right; case); simpl.
      have [<- | neqx] := term_eqP a1 a2; last (by right; case); simpl.
      by constructor.
    - match goal with |- reflect _ (?f cs1 cs2) => set cases_eq := f end.
      assert (cases_eqP : Equality.axiom cases_eq).
      {
        clear cs1 cs2.
        move; elim=> [| [p1 t1] cs1 IH] [| [p2 t2] cs2] //=; try by constructor.
        have [<- | neqx] := p1 =P p2; last (by right; case); simpl.
        have [<- | neqx] := term_eqP t1 t2; last (by right; case); simpl.
        have [<- | neqx] := IH cs2; last (by right; case); simpl.
        by constructor.
      }
      have [<- | neqx] := cases_eqP cs1 cs2; last (by right; case); simpl.
      by constructor.
  Qed.

  (* EqType canonical structures *)
  Definition term_eqMixin := EqMixin term_eqP.
  Canonical term_eqType := EqType term term_eqMixin.

End eq.

(* Constructor coercions *)
Coercion TVariable : variable >-> term.
Coercion TFlexible x := TVariable (VF x).
Coercion TRigid x := TVariable (VR x).
Coercion TConstructor : constructor >-> term.
Coercion TFunction : function >-> term.
Coercion TUnknown : unknown >-> term.

(* Notation scopes *)
Declare Scope term_scope.
Bind Scope term_scope with term.
Delimit Scope term_scope with term.
Declare Scope case_scope.
Delimit Scope case_scope with case.
Declare Scope cases_scope.
Delimit Scope cases_scope with cases.

Notation "{-t t -}" := (t%term)
  (at level 0, t at level 100, no associativity, only parsing).

(* Constructor notations *)
Notation "$( i , j )" := (TParameter (P i j))
  (at level 0, i at level 0, j at level 0, no associativity,
  format "'$(' i ','  j ')'") : term_scope.
Notation "$ j" := (TParameter (P 0 j))
  (at level 0, j at level 0, no associativity, format "'$' j") : term_scope.
Notation "$$ i" := (TParameter (P i 0))
  (at level 0, i at level 0, no associativity, format "'$$' i") : term_scope.
Notation "? x" := (TVariable (x : variable))
  (at level 0, x at level 0, no associativity, format "'?' x") : term_scope.
Notation "f ' a" := (TApplication f a)
  (at level 10, left associativity) : term_scope.
Notation "match: cs" := (TMatch (cs%cases : match_cases))
  (at level 20, right associativity, cs at level 0) : term_scope.
Notation "p -> b" := ((p%pattern : pattern, b%term : term) : match_case)
  (only parsing) : case_scope.
Notation "{ }" := ([::]) (only parsing) : cases_scope.
Notation "{ c1 | .. | cn }" := (c1%case :: (.. [:: cn%case] ..))
  (only parsing) : cases_scope.

(* Derived constructor notations for pairs *)
Definition TPair x1 x2 := {-t CPair ' x1 ' x2 -}.
Notation "( x1 , x2 , .. , xn )" := (TPair (.. (TPair x1 x2) ..) xn)
  : term_scope.

(* Derived constructor notations for booleans *)
Definition TTrue := TConstructor CTrue.
Definition TFalse := TConstructor CFalse.
Definition term_of_bool b := if b then TTrue else TFalse.
Coercion term_of_bool : bool >-> term.

(* Derived constructor notations for naturals *)
Definition TZero := TConstructor CZero.
Definition TSucc n := {-t CSucc ' n -}.
Notation "n .+1" := (TSucc n) : term_scope.
Fixpoint term_of_nat n :=
  match n with
  | 0 => TZero
  | n.+1 => TSucc (term_of_nat n)
  end.
Fixpoint nat_of_term t :=
  match t with
  | TConstructor CZero => Some 0
  | TApplication (TConstructor CSucc) t' =>
    match nat_of_term t' with
    | Some n' => Some (n'.+1)
    | None => None
    end
  | _ => None
  end.
Definition term_of_uint n :=
  term_of_nat (Nat.of_num_uint n).
Definition uint_of_term t :=
  match nat_of_term t with
  | Some t' => Some (Nat.to_num_uint t')
  | None => None
  end.
Numeral Notation term term_of_uint uint_of_term : term_scope.

(* Derived constructor notations for lists *)
Definition TNil := TConstructor CNil.
Notation "[ ]" := TNil : term_scope.
Definition TCons x xs := {-t CCons ' x ' xs -}.
Notation "x :: xs" := (TCons x xs) : term_scope.
Notation "[ x1 , .. , xn ]" := {-t x1 :: (.. (xn :: []) ..) -}
  : term_scope.
Fixpoint term_of_list ts :=
  match ts with
  | [::] => TNil
  | t :: ts => TCons t (term_of_list ts)
  end.
Fixpoint list_of_term t :=
  match t with
  | TConstructor CNil => Some [::]
  | TApplication (TApplication (TConstructor CCons) t') ts =>
    match list_of_term ts with
    | Some ts' => Some (t' :: ts')
    | None => None
    end
  | _ => None
  end.

(* Derived constructor notations for matching *)
Definition TMatchWith s cs := {-t (match: cs) ' s -}.
Notation "match: s with: cs" := (TMatchWith s%term cs%cases)
  (at level 20, right associativity, s at level 0, cs at level 0) : term_scope.
Definition TAbstraction b := {-t match: { $0 -> b } -}.
Notation "fun: b" := (TAbstraction b%term)
  (at level 20, right associativity, b at level 100) : term_scope.
Definition TLet s p b := {-t match: s with: { p -> b } -}.
Notation "let: p := s in: b" := (TLet s%term p%pattern b%term)
  (at level 20, right associativity, s at level 100, b at level 100)
  : term_scope.
Definition TIf s tb fb := {-t
  match: s with:
  { true -> tb
  | false -> fb
  }
-}.
Notation "if: s then: tb else: fb" := (TIf s%term tb%term fb%term)
  (at level 20, right associativity, s at level 100, tb at level 100,
    fb at level 100) : term_scope.

(* Pair operations *)
Definition TFirst p := {-t let: ($0, %) := p in: $0 -}.
Notation "p .1" := (TFirst p) : term_scope.
Definition TSecond p := {-t let: (%, $0) := p in: $0 -}.
Notation "p .2" := (TSecond p) : term_scope.

(* Boolean operations *)
Definition TNot b := {-t if: b then: false else: true -}.
Notation "~~ b" := (TNot b) : term_scope.
Definition TOr b1 b2 := {-t
  if: b1 then: true else:
  if: b2 then: true else:
  false
-}.
Notation "b1 || b2" := (TOr b1 b2) : term_scope.
Definition TAnd b1 b2 := {-t ~~(~~b1 || ~~b2) -}.
Notation "b1 && b2" := (TAnd b1 b2) : term_scope.

(* Function notations for boolean equality *)
Definition TEqual x1 x2 := {-t FEqual ' x1 ' x2 -}.
Notation "x1 == x2" := (TEqual x1 x2) : term_scope.
Definition TNotEqual x1 x2 := {-t ~~(x1 == x2) -}.
Notation "x1 != x2" := (TNotEqual x1 x2) : term_scope.

(* Function notations for naturals *)
Definition TAdd x1 x2 := {-t FAdd ' x1 ' x2 -}.
Notation "x1 + x2" := (TAdd x1 x2) : term_scope.

(* Function notations for lists *)
Definition TIn y xs := {-t FCount ' y ' xs != 0 -}.
Notation "y \in xs" := (TIn y xs) : term_scope.
Definition TNotIn y xs := {-t ~~(y \in xs) -}.
Notation "y \notin xs" := (TNotIn y xs) : term_scope.
Definition TConcat xs ys := {-t FConcat ' xs ' ys -}.
Notation "xs ++ ys" := (TConcat xs ys) : term_scope.
Definition TSetUnion xs ys := {-t FSetUnion ' xs ' ys -}.
Notation "xs :|: ys" := (TSetUnion xs ys) : term_scope.

(* Tactics *)
Ltac dfold_term :=
  repeat match goal with
  (* Derived constructor notations for pairs *)
  | |- context[ {-t TConstructor CPair ' ?x1 ' ?x2 -} ] => rewrite -/(TPair x1 x2)

  (* Derived constructor notations for booleans *)
  | |- context[ {-t TConstructor CTrue -} ] => rewrite -/TTrue
  | |- context[ {-t TConstructor CFalse -} ] => rewrite -/TFalse

  (* Derived constructor notations for lists *)
  | |- context[ {-t TConstructor CNil -} ] => rewrite -/TNil
  | |- context[ {-t TConstructor CCons ' ?x ' ?xs -} ] => rewrite -/(TCons x xs)

  (* Derived constructor notations for matching *)
  | |- context[ {-t (match: ?cs) ' ?s -} ] => rewrite -/(TMatchWith s cs)
  | |- context[ {-t match: { $0 -> ?b } -} ] => rewrite -/(TAbstraction b)
  | |- context[ {-t match: ?s with: { ?p -> ?b } -} ] => rewrite -/(TLet s p b)
  | |- context[ {-t
    match: ?s with:
    { true -> ?tb
    | false -> ?fb
    }
  -} ] => rewrite -/(TIf s tb fb)

  (* Pair operations *)
  | |- context[ {-t let: ($0, %) := ?p in: $0 -} ] => rewrite -/(TFirst p)
  | |- context[ {-t let: (%, $0) := ?p in: $0 -} ] => rewrite -/(TSecond p)

  (* Boolean operations *)
  | |- context[ {-t if: ?b then: false else: true -} ] => rewrite -/(TNot b)
  | |- context[ {-t
    if: ?b1 then: true else:
    if: ?b2 then: true else:
    false
  -} ] => rewrite -/(TOr b1 b2)
  | |- context[ {-t ~~(~~?b1 || ~~?b2) -} ] => rewrite -/(TAnd b1 b2)

  (* Function notations for boolean equality *)
  | |- context[ {-t FEqual ' ?x1 ' ?x2 -} ] => rewrite -/(TEqual x1 x2)
  | |- context[ {-t ~~(?x1 == ?x2) -} ] => rewrite -/(TNotEqual x1 x2)

  (* Function notations for naturals *)
  | |- context[ {-t FAdd ' ?x1 ' ?x2 -} ] => rewrite -/(TAdd x1 x2)

  (* Function notations for lists *)
  | |- context[ {-t FCount ' ?y ' ?xs != 0 -} ] => rewrite -/(TIn y xs)
  | |- context[ {-t ~~(?y \in ?xs) -} ] => rewrite -/(TNotIn y xs)
  | |- context[ {-t FConcat ' ?xs ' ?ys -} ] => rewrite -/(TConcat xs ys)
  | |- context[ {-t FSetUnion ' ?xs ' ?ys -} ] => rewrite -/(TSetUnion xs ys)
  end.
