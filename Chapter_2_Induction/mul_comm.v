From LF Require Import Basics.
From LF Require Import basic_intro.

Theorem add_shuffle3 : forall n m p : nat,
  n + (m + p) = m + (n + p).
Proof.
  intros n m p.
  assert (H: n+m = m+n).
  {rewrite add_comm. reflexivity. }
  rewrite add_assoc. rewrite H.
  rewrite add_assoc. reflexivity.
Qed.

Theorem mul_1_r : forall m : nat,
  m * 1 = m.
Proof.
  induction m as [| m' IH].
  - reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.

Theorem plus_one : forall m n: nat,
  m * S n = m * n + m.
Proof.
  intros m n. induction m as [| m' IHm'].
  - reflexivity.
  - simpl. rewrite IHm'.
    rewrite add_assoc.
    rewrite <- plus_1_l.
    rewrite add_assoc. rewrite add_assoc.
    rewrite add_comm.
    rewrite add_assoc.
    rewrite add_assoc.
    assert (H: m'+1 = S m').
    {rewrite add_comm. reflexivity. }
    rewrite H.
    rewrite add_comm.
    rewrite add_assoc.
    rewrite add_comm.
    rewrite add_assoc.
    reflexivity.
Qed.

Theorem plus_one_b : forall m n: nat,
  S n * m = n * m + m.
Proof.
  intros m n. induction m as [| m' IHm'].
  - rewrite mult_O_r. rewrite mult_O_r.
    reflexivity.
  - rewrite add_comm.
    simpl. reflexivity.
Qed.

Theorem mul_comm : forall m n : nat,
  m * n = n * m.
Proof.
  intros m n. induction n as [| n' IHn'].
  - simpl. rewrite mult_O_r. reflexivity.
  - rewrite plus_one.
    rewrite plus_one_b.
    rewrite IHn'.
    reflexivity.
Qed.
