Require Import List.
Import ListNotations.

Lemma in_singleton_eq [A : Type] : forall (x a : A), In x [a] -> a = x.
Proof.
  intros x a H. destruct H as [H|H].
  - assumption.
  - contradiction.
Qed.


Lemma incl_cons_cons [A : Type] (l l' : list A) (a : A) : incl l l' -> incl (a :: l) (a :: l').
Proof.
  intro H. apply incl_cons; try now left. apply incl_tl. assumption.
Qed.
