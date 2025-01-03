Fixpoint is_even (n : nat) : bool :=
  match n with
  | O       => true
  | S O     => false
  | S (S m) => is_even m
  end.

Definition odd (n : nat) : Prop :=
  exists m, n = 2 * m + 1.

Inductive even : nat -> Prop :=
| even_O : even O
| even_SS : forall n, even n -> even (S (S n)).

Compute (is_even 12).

Fixpoint double (n : nat) :=
  match n with
  | O   => O
  | S m => S (S (double m))
  end.

Theorem even_double : forall n, even (double n).
Proof.
induction n.
- simpl. apply even_O.
- simpl. apply even_SS. assumption.
Qed.
