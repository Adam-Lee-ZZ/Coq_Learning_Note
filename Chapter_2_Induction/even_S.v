From LF Require Export Basics.

Theorem even_S : forall n : nat,
  evenb (S n) = negb (evenb n).
Proof.
  intros n. induction n as [| n' IHn'].
  - reflexivity.
  -rewrite IHn'. simpl. rewrite negb_involutive.
    reflexivity.
Qed.
