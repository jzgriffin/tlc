Require Import Coq.Lists.List.
Require Import TLC.Word.

Import ListNotations.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Infix "^::" := combine
  (at level 60, right associativity) : word_scope.

Definition byte := word 8.
Definition bytes := list byte.

Definition word16_halves (x : word 16) : byte * byte :=
  (split1 8 8 x, split2 8 8 x).
Definition word32_halves (x : word 32) : word 16 * word 16 :=
  (split1 16 16 x, split2 16 16 x).
Definition word64_halves (x : word 64) : word 32 * word 32 :=
  (split1 32 32 x, split2 32 32 x).
Definition word128_halves (x : word 128) : word 64 * word 64 :=
  (split1 64 64 x, split2 64 64 x).

Definition halves_word n (p : word n * word n) :=
  match p with (l, r) => combine l r end.

Definition pair_to_list T (p : T * T) : list T :=
  match p with (l, r) => [l; r] end.
Definition list_to_pair T (l : list T) : option (T * T) :=
  match l with
  | [l; r] => Some (l, r)
  | _ => None
  end.

Fixpoint list_to_pairs T (xs : list T) (dx : T) : list (T * T) :=
  match xs with
  | lx :: rx :: xs' => (lx, rx) :: list_to_pairs xs' dx
  | [lx] => [(lx, dx)]
  | [] => []
  end.

Definition bytes_to_word16s (bs : bytes) : list (word 16) :=
  map (fun p => halves_word p) (list_to_pairs bs $0).
Definition word16s_to_word32s (ws : list (word 16)) : list (word 32) :=
  map (fun p => halves_word p) (list_to_pairs ws $0).
Definition bytes_to_word32s (bs : bytes) : list (word 32) :=
  word16s_to_word32s (bytes_to_word16s bs).
Definition word32s_to_word64s (ws : list (word 32)) : list (word 64) :=
  map (fun p => halves_word p) (list_to_pairs ws $0).
Definition bytes_to_word64s (bs : bytes) : list (word 64) :=
  word32s_to_word64s (bytes_to_word32s bs).
Definition word64s_to_word128s (ws : list (word 64)) : list (word 128) :=
  map (fun p => halves_word p) (list_to_pairs ws $0).
Definition bytes_to_word128s (bs : bytes) : list (word 128) :=
  word64s_to_word128s (bytes_to_word64s bs).

Definition word16_to_bytes (x : word 16) : bytes :=
  pair_to_list (word16_halves x).
Definition word32_to_word16s (x : word 32) : list (word 16) :=
  pair_to_list (word32_halves x).
Definition word64_to_word32s (x : word 64) : list (word 32) :=
  pair_to_list (word64_halves x).
Definition word128_to_word64s (x : word 128) : list (word 64) :=
  pair_to_list (word128_halves x).

Definition word32_to_bytes (x : word 32) : bytes :=
  match word32_halves x with (l, r) =>
    word16_to_bytes l ++ word16_to_bytes r end.
Definition word64_to_bytes (x : word 64) : bytes :=
  match word64_halves x with (l, r) =>
    word32_to_bytes l ++ word32_to_bytes r end.
Definition word128_to_bytes (x : word 128) : bytes :=
  match word128_halves x with (l, r) =>
    word64_to_bytes l ++ word64_to_bytes r end.

Definition word16s_to_bytes (ws : list (word 16)) : bytes :=
  List.fold_left (fun bs w => bs ++ word16_to_bytes w) ws [].
Definition word32s_to_bytes (ws : list (word 32)) : bytes :=
  List.fold_left (fun bs w => bs ++ word32_to_bytes w) ws [].
Definition word64s_to_bytes (ws : list (word 64)) : bytes :=
  List.fold_left (fun bs w => bs ++ word64_to_bytes w) ws [].
Definition word128s_to_bytes (ws : list (word 128)) : bytes :=
  List.fold_left (fun bs w => bs ++ word128_to_bytes w) ws [].
