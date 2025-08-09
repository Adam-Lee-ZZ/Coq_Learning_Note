Theorem identity_fn_applied_twice :
  forall (f : bool -> bool),
  (forall (x : bool), f x = x) ->
  forall (b : bool), f (f b) = b.
Proof.
  intros f H b.
  rewrite H.
  rewrite H.
  reflexivity.
Qed.

Theorem andb_eq_orb :
  forall (b c : bool),
  (andb b c = orb b c) ->
  b = c.
Proof.
    intros b c.
    destruct b eqn:Eb.
    - destruct c eqn:Ec.
        -- simpl.
            reflexivity.
        -- simpl.
            intros H.
            rewrite H.
            reflexivity.
    - destruct c eqn:Ec.
        -- simpl.
            intros H.
            rewrite H.
            reflexivity.
        -- simpl.
            reflexivity.
Qed.


  