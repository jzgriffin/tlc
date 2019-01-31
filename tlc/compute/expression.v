Require Import Coq.funind.Recdef.
Require Import mathcomp.ssreflect.eqtype.
Require Import mathcomp.ssreflect.seq.
Require Import mathcomp.ssreflect.ssrbool.
Require Import mathcomp.ssreflect.ssreflect.
Require Import mathcomp.ssreflect.ssrnat.
Require Import tlc.compute.constructor.
Require Import tlc.compute.function.
Require Import tlc.compute.variable.
Require Import tlc.utility.monad.
Require Import tlc.utility.option.
Require Import tlc.utility.partial_map.
Require Import tlc.utility.result.
Require Import tlc.utility.set.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Expression type *)
Inductive expression : Type :=
| EConstructor : constructor -> expression
| EFunction : function -> expression
| EVariable : variable -> expression
| EApplication : expression -> expression -> expression
| EAbstraction : variable -> expression -> expression
| ELet : variable -> expression -> expression -> expression.

(* Constructor coercions *)
Coercion EConstructor : constructor >-> expression.
Coercion EFunction : function >-> expression.
Coercion EVariable : variable >-> expression.

(* Notation scope *)
Delimit Scope expression_scope with e.
Bind Scope expression_scope with expression.
Notation "{e: e }" := (e%e) (at level 0, e at level 99, no associativity,
  only parsing).

(* Expression constructor notations *)
Notation "% c" := (EConstructor c)
  (at level 0, c at level 0, no associativity, only parsing, format "'%' c")
  : expression_scope.
Notation "# f" := (EFunction f)
  (at level 0, f at level 0, no associativity, only parsing, format "'#' f")
  : expression_scope.
Notation "$ v" := (EVariable v)
  (at level 0, v at level 0, no associativity, only parsing, format "'$' v")
  : expression_scope.
Notation "ef $ ea" := (EApplication ef ea)
  (at level 10, left associativity) : expression_scope.
Notation "\ v , eb" := (EAbstraction v eb)
  (at level 20, right associativity, eb at level 99, format "'\' v ','  eb")
  : expression_scope.
Notation "'let:' v := ev 'in' eb" := (ELet v ev eb)
  (at level 20, right associativity, ev at level 99, eb at level 99)
  : expression_scope.

(* Constructor expression notations *)
Notation "( e1 , e2 , .. , en )" :=
  {e: CPair $ (.. (CPair $ e1 $ e2) ..) $ en} : expression_scope.
Notation "[ ]" := {e: %CNil} : expression_scope.
Notation "e :: es" := {e: CCons $ e $ es} : expression_scope.
Notation "[ e ]" := {e: e :: []} : expression_scope.
Notation "[ e1 , .. , en ]" := {e: e1 :: (.. (CCons $ en $ []) ..)}
  : expression_scope.

(* Function expression notations *)
Notation "el = er" := {e: FEqual $ el $ er} : expression_scope.
Notation "e \in es" := {e: FMember $ e $ es} : expression_scope.
Notation "el + er" := {e: FAdd $ el $ er} : expression_scope.
Notation "esl \union esr" := {e: FUnion $ esl $ esr}
  (at level 50, left associativity) : expression_scope.

(* Boolean conversion *)
Definition EBoolean b :=
  match b with
  | true => {e: %CTrue}
  | false => {e: %CFalse}
  end.
Coercion EBoolean : bool >-> expression.

(* Natural conversion *)
Fixpoint ENatural n :=
  match n with
  | O => {e: %CZero}
  | S n' => {e: %CSucc $ (ENatural n')}
  end.
Coercion ENatural : nat >-> expression.

(* List conversion *)
Fixpoint EList xs :=
  match xs with
  | [::] => {e: []}
  | x :: xs => {e: x :: EList xs}
  end.

(* Equality *)
Section eq.

  (* Boolean equality *)
  Fixpoint expression_eq el er :=
    match el, er with
    | EConstructor cl, EConstructor cr => cl == cr
    | EConstructor _, _ => false
    | EFunction fl, EFunction fr => fl == fr
    | EFunction _, _ => false
    | EVariable vl, EVariable vr => vl == vr
    | EVariable _, _ => false
    | EApplication efl eal, EApplication efr ear =>
      expression_eq efl efr && expression_eq eal ear
    | EApplication _ _, _ => false
    | EAbstraction vl ebl, EAbstraction vr ebr =>
      (vl == vr) && expression_eq ebl ebr
    | EAbstraction _ _, _ => false
    | ELet vl evl ebl, ELet vr evr ebr =>
      (vl == vr) && expression_eq evl evr && expression_eq ebl ebr
    | ELet _ _ _, _ => false
    end.

  (* Boolean equality reflection *)
  Lemma expression_eqP : Equality.axiom expression_eq.
  Proof.
    elim=>
      [cl | fl | vl | efl IHef eal IHea | vl ebl IHeb | vl evl IHev ebl IHeb]
      [cr | fr | vr | efr ear | vr ebr | vr evr ebr] //=; try by constructor.
    - case H: (cl == cr); move/eqP: H => H; constructor; first by rewrite H.
      by move=> [].
    - case H: (fl == fr); move/eqP: H => H; constructor; first by rewrite H.
      by move=> [].
    - case H: (vl == vr); move/eqP: H => H; constructor; first by rewrite H.
      by move=> [].
    - case Hef: (expression_eq efl efr); move/IHef: Hef => Hef //=; subst;
        last by constructor; move=> [].
      case Hea: (expression_eq eal ear); move/IHea: Hea => Hea //=; subst;
        last by constructor; move=> [].
      by constructor.
    - case Hv: (vl == vr); move/eqP: Hv => Hv //=; subst;
        last by constructor; move=> [].
      case Heb: (expression_eq ebl ebr); move/IHeb: Heb => Heb //=; subst;
        last by constructor; move=> [].
      by constructor.
    - case Hv: (vl == vr); move/eqP: Hv => Hv //=; subst;
        last by constructor; move=> [].
      case Hev: (expression_eq evl evr); move/IHev: Hev => Hev //=; subst;
        last by constructor; move=> [].
      case Heb: (expression_eq ebl ebr); move/IHeb: Heb => Heb //=; subst;
        last by constructor; move=> [].
      by constructor.
  Qed.

  (* EqType canonical structures *)
  Canonical Structure expression_eqMixin := EqMixin expression_eqP.
  Canonical Structure expression_eqType :=
    Eval hnf in EqType expression expression_eqMixin.

End eq.

(* Height of an expression tree *)
Fixpoint height e :=
  match e with
  | EConstructor _
  | EFunction _
  | EVariable _ => 0
  | EAbstraction _ e => height e
  | EApplication e1 e2
  | ELet _ e1 e2 => maxn (height e1) (height e2)
  end.+1.

(* Free variables within an expression *)
Local Fixpoint fv e : set [eqType of variable] :=
  match e with
  | EConstructor _
  | EFunction _ => [::]
  | EVariable x => [:: x]
  | EApplication e1 e2
  | ELet _ e1 e2 => fv e1 {+} fv e2
  | EAbstraction x e => rem x (fv e)
  end.

(* Changes the name of a variable within an expression *)
Fixpoint change_variable x x' e :=
  match e with
  | EConstructor _
  | EFunction _ => e
  | EVariable y => if x == y then x' else y
  | EApplication ef ea =>
    EApplication (change_variable x x' ef) (change_variable x x' ea)
  | EAbstraction y eb =>
    if x == y then e else EAbstraction y (change_variable x x' eb)
  | ELet y ex eb =>
    if x == y then ELet y (change_variable x x' ex) eb
    else ELet y (change_variable x x' ex) (change_variable x x' eb)
  end.

Lemma height_change_variable x x' e :
  height (change_variable x x' e) = height e.
Proof.
  elim: e =>
    [c | f | v | e1 IHe1 e2 IHe2 | v e1 IHe1 | v e1 IHe1 e2 IHe2] //=;
    (try by rewrite IHe1 IHe2); case (x == v) => //=;
    (try by rewrite IHe1); (try by rewrite IHe1 IHe2).
Qed.

(* Capture-avoiding variable-to-expression substitution *)
Function substitute x e' e {measure height e} :=
  match e with
  | EConstructor _
  | EFunction _ => e
  | EVariable y => if x == y then e' else e
  | EApplication ef ea =>
    EApplication (substitute x e' ef) (substitute x e' ea)
  | EAbstraction y eb =>
    if x == y then e
    else
      if y \notin fv e' then EAbstraction y (substitute x e' eb)
      else
        let y' := fresh_variable y (fv e ++ fv e') in
        EAbstraction y' (substitute x e' (change_variable y y' eb))
  | ELet y ey eb => ELet y (substitute x e' ey) (substitute x e' eb)
  end.
Proof.
  all: move=> *; apply/ltP=> //=; rewrite ltnS;
    try apply leq_maxr; try apply leq_maxl.
  by rewrite height_change_variable //=.
Defined.

(* Decision of normal form *)
Fixpoint is_normal e :=
  match e with
  | EConstructor _ => true
  | EFunction _ => true
  | EVariable _ => false
  | EApplication ef ea =>
    if ef is EAbstraction _ _ then false
    else is_normal ef && is_normal ea
  | EAbstraction _ eb => true
  | ELet _ _ _ => false
  end.

(* Expression evaluation environment *)
Definition environment := partial_map [eqType of variable] expression.

(* Expression evaluation errors *)
Inductive evaluation_error : Type :=
| EEFuel : evaluation_error
| EEBoolean : evaluation_error
| EENatural : evaluation_error
| EEList : evaluation_error
| EEMap : evaluation_error.

(* Evaluation result *)
Definition evaluation_result := result evaluation_error.

(* Boolean expression lifting *)
Definition lift_boolean (e : expression) :=
  match e with
  | {e: %CTrue} => pure true
  | {e: %CFalse} => pure false
  | _ => Error EEBoolean
  end.

(* Natural expression lifting *)
Fixpoint lift_natural x :=
  match x with
  | {e: %CZero} => pure 0
  | {e: %CSucc $ x} => n <- lift_natural x; pure n.+1
  | _ => Error EENatural
  end.

(* List expression lifting *)
Fixpoint lift_list xs :=
  match xs with
  | {e: []} => pure [::]
  | {e: x :: xs} => xs <- lift_list xs; pure (x :: xs)
  | _ => Error EEList
  end.

(* Expression evaluation *)
Fixpoint evaluate' fuel (E : environment) e :=
  if fuel is S fuel then
    match e with
    | EConstructor _
    | EFunction _ => pure e
    | EVariable v => pure (if E{@v} is Some e' then e' else e)
    | EApplication ef ea =>
      ef <- evaluate' fuel E ef;
      ea <- evaluate' fuel E ea;
      if ef is EAbstraction v eb then evaluate' fuel E{= v := ea} eb
      else
        let e := EApplication ef ea in
        if is_normal e then
          (* External function evaluation *)
          match e with
          (* Any *)
          | {e: x = y} => pure (EBoolean (x == y))
          (* Natural *)
          | {e: x + y} =>
            x <- lift_natural x;
            y <- lift_natural y;
            pure (ENatural (x + y))
          (* List *)
          | {e: x \in xs} =>
            xs <- lift_list xs;
            pure (EBoolean (x \in xs))
          | {e: FCount $ x $ xs} =>
            xs <- lift_list xs;
            pure (ENatural (count_mem x xs))
          | {e: xs \union ys} =>
            xs <- lift_list xs;
            ys <- lift_list ys;
            pure (EList (xs {+} ys))
          | {e: FMap $ f $ xs} =>
            xs <- lift_list xs;
            evaluate' fuel E (EList [seq {e: f $ x} | x <- xs])
          (* Default *)
          | _ => pure e
          end
        else pure e
    | EAbstraction v eb =>
      eb <- evaluate' fuel E{-v} eb;
      pure (EAbstraction v eb)
    | ELet v ev eb =>
      ev <- evaluate' fuel E ev;
      evaluate' fuel E{= v := ev} eb
    end
  else Error EEFuel.

(* Evaluation with a default amount of fuel *)
Definition evaluate_fuel := 4999.
Definition evaluate := evaluate' evaluate_fuel.
