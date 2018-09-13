From mathcomp.ssreflect
Require Import ssreflect eqtype ssrbool ssrnat seq path.
From tlc.utility
Require Import seq.

Require Export message_variable node_variable general_variable.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Inductive variable : Type :=
| Vnode : node_variable -> variable
| Vmessage : message_variable -> variable
| Vgeneral : general_variable -> variable.

(* Equality *)
Section variable_eq.

  Definition eq_variable (x x' : variable) :=
    match x, x' with
    | Vnode nx, Vnode nx' => nx == nx'
    | Vnode _, _ => false
    | Vmessage mx, Vmessage mx' => mx == mx'
    | Vmessage _, _ => false
    | Vgeneral gx, Vgeneral gx' => gx == gx'
    | Vgeneral _, _ => false
    end.

  Lemma eq_variableP : Equality.axiom eq_variable.
  Proof.
    case=> [nx | mx | gx]; case=> [nx' | mx' | gx'];
      rewrite /eq_variable /=; try by constructor.
    - (* Vnode *)
      case Hnx: (nx == nx');
        [move/eqP: Hnx => ?; subst nx' | constructor];
        last by case=> ?; subst nx'; rewrite eqxx in Hnx.
      by constructor.
    - (* Vmessage *)
      case Hmx: (mx == mx');
        [move/eqP: Hmx => ?; subst mx' | constructor];
        last by case=> ?; subst mx'; rewrite eqxx in Hmx.
      by constructor.
    - (* Vgeneral *)
      case Hgx: (gx == gx');
        [move/eqP: Hgx => ?; subst gx' | constructor];
        last by case=> ?; subst gx'; rewrite eqxx in Hgx.
      by constructor.
  Qed.

  Canonical variable_eqMixin :=
    Eval hnf in EqMixin eq_variableP.
  Canonical variable_eqType :=
    Eval hnf in EqType variable variable_eqMixin.

End variable_eq.

(* Coercions *)
Coercion Vnode : node_variable >-> variable.
Coercion Vmessage : message_variable >-> variable.
Coercion Vgeneral : general_variable >-> variable.

(* Arbitrary variables *)
Definition next_var x :=
  match x with
  | Vnode nx => Vnode (next_node_var nx)
  | Vmessage mx => Vmessage (next_message_var mx)
  | Vgeneral gx => Vgeneral (next_general_var gx)
  end.
Definition fresh_var x xs :=
  match x with
  | Vnode nx =>
    let nxs := osomes [seq
      if x is Vnode nx then Some nx else None | x <- xs] in
    Vnode (fresh_node_var nx nxs)
  | Vmessage mx =>
    let mxs := osomes [seq
      if x is Vmessage mx then Some mx else None | x <- xs] in
    Vmessage (fresh_message_var mx mxs)
  | Vgeneral gx =>
    let gxs := osomes [seq
      if x is Vgeneral gx then Some gx else None | x <- xs] in
    Vgeneral (fresh_general_var gx gxs)
  end.
Lemma fresh_var_unique x xs : ~(fresh_var x xs \in xs).
Proof.
  (* TODO *)
Admitted.
