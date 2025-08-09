Definition andb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => b2
  | false => false
  end.

Theorem andb_true_elim2 : forall b c : bool,
  andb b c = true -> c = true.

(*Proof.
    intros b c.
    destruct b eqn:Eb.
    - simpl. intros H. rewrite H. reflexivity.
    - simpl. intros H. discriminate H.
Qed.*)

Proof.
  intros b c.
  destruct b eqn:Eb.
  - destruct c eqn:Ec.
    -- reflexivity.
    -- intros H.
        rewrite <- H.
        reflexivity.
  - destruct c eqn:Ec.
    -- reflexivity.
    -- intros H.
        rewrite <- H.
        reflexivity.
Qed.