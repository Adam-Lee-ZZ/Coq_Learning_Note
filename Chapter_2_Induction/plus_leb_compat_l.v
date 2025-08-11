From LF Require Import Basics.
Check leb.

Notation "x <=? y" := (leb x y) (at level 70) : nat_scope.
Theorem plus_leb_compat_l : forall n m p : nat,
  n <=? m = true -> (p + n) <=? (p + m) = true.
Proof.
    intros n m p H.
    induction p.
    - simpl. rewrite H.
        reflexivity.
    - simpl. rewrite IHp.
        reflexivity.
Qed.