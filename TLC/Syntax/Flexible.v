Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Flexible variables in the language *)
Inductive flexible : Type :=
| Fn
| Fd
| Fo
| Fe
| Fors
| Fois
| Fs
| Fs'.

(* Decidable equality *)
Lemma flexible_eq_dec (f f' : flexible) : {f = f'} + {f <> f'}.
Proof.
  decide equality.
Defined.

Definition flexible_eqb f f' :=
  match f, f' with
  | Fn, Fn => true
  | Fd, Fd => true
  | Fo, Fo => true
  | Fe, Fe => true
  | Fors, Fors => true
  | Fois, Fois => true
  | Fs, Fs => true
  | Fs', Fs' => true
  | _, _ => false
  end.

Lemma flexible_eqb_refl f : flexible_eqb f f = true.
Proof.
  now destruct f.
Qed.
