Require Import mathcomp.ssreflect.eqtype.
Require Import mathcomp.ssreflect.seq.
Require Import mathcomp.ssreflect.ssrbool.
Require Import mathcomp.ssreflect.ssreflect.
Require Import mathcomp.ssreflect.ssrnat.
Require Import tlc.compute.constructor.
Require Import tlc.compute.function.
Require Import tlc.compute.pattern.
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
| ELet : pattern -> expression -> expression -> expression
| EMatch : expression -> matchings -> expression
with matchings : Type :=
| MSNil : matchings
| MSCons : matching -> matchings -> matchings
with matching : Type :=
| M : pattern -> expression -> matching.

(* Expression constructor coercions *)
Coercion EConstructor : constructor >-> expression.
Coercion EFunction : function >-> expression.
Coercion EVariable : variable >-> expression.

(* Expression notation scope *)
Delimit Scope expression_scope with e.
Bind Scope expression_scope with expression.
Notation "{e: e }" := (e%e) (at level 0, e at level 99, no associativity,
  only parsing).

(* Matching notation scope *)
Delimit Scope matching_scope with m.
Bind Scope matching_scope with matching.
Notation "{m: m }" := (m%m) (at level 0, m at level 99, no associativity,
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
Notation "'let:' p := ep 'in' eb" := (ELet p ep eb)
  (at level 20, right associativity, ep at level 99, eb at level 99)
  : expression_scope.
Notation "'match:' ec 'with' m1 | .. | mn 'end'" :=
  (EMatch ec (MSCons m1%m (.. (MSCons mn%m MSNil) ..)))
  (at level 20, no associativity, ec at level 99, m1, mn at level 99)
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

(* Matching constructor notations *)
Notation "p :=> e" := (M p%p e%e)
  (at level 0, e at level 0, no associativity) : matching_scope.

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
    | ELet pl epl ebl, ELet pr epr ebr =>
      (pl == pr) && expression_eq epl epr && expression_eq ebl ebr
    | ELet _ _ _, _ => false
    | EMatch ecl msl, EMatch ecr msr =>
      expression_eq ecl ecr && matchings_eq msl msr
    | EMatch _ _, _ => false
    end
  with matchings_eq msl msr :=
    match msl, msr with
    | MSNil, MSNil => true
    | MSCons ml msl, MSCons mr msr =>
      matching_eq ml mr && matchings_eq msl msr
    | _, _ => false
    end
  with matching_eq ml mr :=
    match ml, mr with
    | M pl el, M pr er => (pl == pr) && expression_eq el er
    end.

  (* Boolean equality reflection *)
  Fixpoint expression_eqP el er : reflect (el = er) (expression_eq el er)
  with matchings_eqP msl msr : reflect (msl = msr) (matchings_eq msl msr)
  with matching_eqP ml mr : reflect (ml = mr) (matching_eq ml mr).
  Proof.
    (* Expression *)
    elim: el er =>
      [cl | fl | vl | efl IHef eal IHea | vl ebl IHeb | pl epl IHep ebl IHeb
        | ecl IHec msl]
      [cr | fr | vr | efr ear | vr ebr | pr epr ebr | ecr msr] //=;
      try by constructor.
    - case H: (cl == cr); move/eqP: H => H; constructor; first by rewrite H.
      by move=> [].
    - case H: (fl == fr); move/eqP: H => H; constructor; first by rewrite H.
      by move=> [].
    - case H: (vl == vr); move/eqP: H => H; constructor; first by rewrite H.
      by move=> [].
    - case H: (expression_eq efl efr); move/IHef: H => H //=; subst;
        last by constructor; move=> [].
      case H: (expression_eq eal ear); move/IHea: H => H //=; subst;
        last by constructor; move=> [].
      by constructor.
    - case H: (vl == vr); move/eqP: H => H //=; subst;
        last by constructor; move=> [].
      case H: (expression_eq ebl ebr); move/IHeb: H => H //=; subst;
        last by constructor; move=> [].
      by constructor.
    - case H: (pl == pr); move/eqP: H => H //=; subst;
        last by constructor; move=> [].
      case H: (expression_eq epl epr); move/IHep: H => H //=; subst;
        last by constructor; move=> [].
      case H: (expression_eq ebl ebr); move/IHeb: H => H //=; subst;
        last by constructor; move=> [].
      by constructor.
    - case H: (expression_eq ecl ecr); move/IHec: H => H //=; subst;
        last by constructor; move=> [].
      case H: (matchings_eq msl msr); move/matchings_eqP: H => H //=;
        subst; last by constructor; move=> [].
      by constructor.
    (* Matchings *)
    elim: msl msr => [| ml msl IHms] [| mr msr] //=; try by constructor.
    - case H: (matching_eq ml mr); move/matching_eqP: H => H //=; subst;
        last by constructor; move=> [].
      case H: (matchings_eq msl msr); move/IHms: H => H //=; subst;
        last by constructor; move=> [].
      by constructor.
    (* Matching *)
    case: ml mr => [pl el] [pr er] //=; try by constructor.
    case H: (pl == pr); move/eqP: H => H //=; subst;
      last by constructor; move=> [].
    case H: (expression_eq el er); move/expression_eqP: H => H //=; subst;
      last by constructor; move=> [].
    by constructor.
  Qed.

  (* EqType canonical structures for expression *)
  Canonical Structure expression_eqMixin := EqMixin expression_eqP.
  Canonical Structure expression_eqType :=
    Eval hnf in EqType expression expression_eqMixin.

  (* EqType canonical structures for matchings *)
  Canonical Structure matchings_eqMixin := EqMixin matchings_eqP.
  Canonical Structure matchings_eqType :=
    Eval hnf in EqType matchings matchings_eqMixin.

  (* EqType canonical structures for matching *)
  Canonical Structure matching_eqMixin := EqMixin matching_eqP.
  Canonical Structure matching_eqType :=
    Eval hnf in EqType matching matching_eqMixin.

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
  | EMatch ec ms => maxn (height ec) (msheight ms)
  end.+1
with msheight ms :=
  match ms with
  | MSNil => 0
  | MSCons m ms => maxn (mheight m) (msheight ms)
  end
with mheight m :=
  match m with
  | M p e => height e
  end.

(* Free variables within an expression *)
Fixpoint fv e : set [eqType of variable] :=
  match e with
  | EConstructor _
  | EFunction _ => [::]
  | EVariable x => [:: x]
  | EApplication e1 e2
  | ELet _ e1 e2 => fv e1 {+} fv e2
  | EAbstraction x e => rem x (fv e)
  | EMatch e ms => fv e {+} msfv ms
  end
with msfv ms : set [eqType of variable] :=
  match ms with
  | MSNil => [::]
  | MSCons m ms => mfv m {+} msfv ms
  end
with mfv m : set [eqType of variable] :=
  match m with
  | M p e => fv e {-} pv p
  end.

(* Decision of closed form *)
Definition is_closed e := nilp (fv e).

(* Transformation to closed form *)
Definition close e := foldr (fun v e => {e: \v, e}) e (fv e).

(* Expression evaluation environment *)
Definition environment := partial_map [eqType of variable] expression.

(* Expression evaluation errors *)
Inductive evaluation_error : Type :=
| EEFuel : evaluation_error
| EEBoolean : evaluation_error
| EENatural : evaluation_error
| EEList : evaluation_error
| EEMap : evaluation_error
| EEMatch : evaluation_error.

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

(* Matchings lifting *)
Fixpoint lift_matchings ms :=
  match ms with
  | MSNil => [::]
  | MSCons m ms => m :: lift_matchings ms
  end.

(* Pattern matching *)
Fixpoint match_pattern e p : evaluation_result environment :=
  match p with
  | PConstructor c =>
    if e is EConstructor c then pure [::]
    else Error EEMatch
  | PVariable v => pure [::] {= v := e}
  | PApplication pl pr =>
    if e is EApplication el er then
      El <- match_pattern el pl;
      Er <- match_pattern er pr;
      pure (pm_union El Er)
    else Error EEMatch
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
        if is_closed e then
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
    | ELet p ep eb =>
      ep <- evaluate' fuel E ep;
      Em <- match_pattern ep p;
      evaluate' fuel (pm_union Em E) eb
    | EMatch ec ms =>
      ec <- evaluate' fuel E ec;
      foldr (fun '(M p e) r =>
        if r is Error _ then
          Em <- match_pattern ec p;
          evaluate' fuel (pm_union Em E) e
        else r) (Error EEMatch) (lift_matchings ms)
    end
  else Error EEFuel.

(* Evaluation with a default amount of fuel *)
Definition evaluate_fuel := 4999.
Definition evaluate := evaluate' evaluate_fuel.
