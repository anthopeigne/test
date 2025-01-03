Require Import Bool.


Definition nxorb (b1 b2 : bool) : bool := if b1 then b2 else negb b2.

Lemma eqb_nxorb : forall b1 b2 b3, eqb (nxorb b1 b2) (nxorb b3 b2) = eqb b1 b3.
Proof. intros [|] [|] [|]; reflexivity. Qed.

Lemma eqb_nxorb_swap : forall b1 b2 b3, eqb (nxorb b1 b2) b3 = eqb b1 (nxorb b3 b2).
Proof. intros [|] [|] [|]; reflexivity. Qed.

Lemma nxorb_invol : forall b1 b2, nxorb (nxorb b1 b2) b2 = b1.
Proof. intros [|] [|]; reflexivity. Qed.
