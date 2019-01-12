Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Basic types of terms in the language *)
Inductive type : Type :=
| TUnit
| TFunction (t1 t2 : type)
| TProduct (t1 t2 : type)
| TSum (t1 t2 : type)
| TList (t1 : type)
| TNatural
| TOrientation
(* Parameters *)
| TNode
| TMessage
(* Periodic events *)
| TPEvent
(* Fair-loss link *)
| TFLLRequest
| TFLLIndication
(* Stubborn link *)
| TSLState
| TSLRequest
| TSLIndication.

(* Notation scope *)
Delimit Scope tlc_type_scope with t.
Bind Scope tlc_type_scope with type.

(* Constructor notations *)
Notation "x -> y" := (TFunction x y) : tlc_type_scope.
Notation "x * y" := (TProduct x y) : tlc_type_scope.
Notation "x + y" := (TSum x y) : tlc_type_scope.
