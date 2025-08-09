Fixpoint plus (n m : nat) : nat :=
  match n with
  | 0 => m
  | S x => S (plus x m)
  end.

Fixpoint mult (n m : nat) : nat :=
  match n with
  | O => O
  | S n' => plus m (mult n' m)
  end.

Fixpoint factorial (n:nat) : nat :=
  match n with
  | 0 => 1
  | S m => mult n (factorial m)
  end.
  
Example test_factorial1: (factorial 3) = 6.
Proof. simpl. reflexivity. Qed.
Example test_factorial2: (factorial 5) = (mult 10 12).
Proof. simpl. reflexivity. Qed.