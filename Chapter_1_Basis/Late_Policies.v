Module LateDays.

Inductive letter : Type :=
  | A | B | C | D | F.

Definition letter_comparison (l1 l2 : letter) : comparison :=
  match l1, l2 with
  | A, A => Eq
  | A, _ => Gt
  | B, A => Lt
  | B, B => Eq
  | B, _ => Gt
  | C, (A | B) => Lt
  | C, C => Eq
  | C, _ => Gt
  | D, (A | B | C) => Lt
  | D, D => Eq
  | D, _ => Gt
  | F, (A | B | C | D) => Lt
  | F, F => Eq
  end.

Theorem letter_comparison_Eq :
  forall l, letter_comparison l l = Eq.
Proof.
    intros [].
    -reflexivity.
    -reflexivity.
    -reflexivity.
    -reflexivity.
    -reflexivity.
Qed.

Inductive modifier : Type :=
  | Plus | Natural | Minus.

Definition modifier_comparison (m1 m2 : modifier) : comparison :=
  match m1, m2 with
  | Plus, Plus => Eq
  | Plus, _ => Gt
  | Natural, Plus => Lt
  | Natural, Natural => Eq
  | Natural, _ => Gt
  | Minus, (Plus | Natural) => Lt
  | Minus, Minus => Eq
  end.

Inductive grade : Type :=
  Grade (l:letter) (m:modifier).

Definition grade_comparison (g1 g2 : grade) : comparison :=
  match g1, g2 with
  | Grade l1 m1, Grade l2 m2 =>
    match letter_comparison l1 l2 with
    | Gt => Gt
    | Lt => Lt
    | Eq =>
        match modifier_comparison m1 m2 with
        | Gt => Gt
        | Lt => Lt
        | Eq => Eq
        end
    end
end.

Example test_grade_comparison1 :
  (grade_comparison (Grade A Minus) (Grade B Plus)) = Gt.
Proof. simpl. reflexivity. Qed.
Example test_grade_comparison2 :
  (grade_comparison (Grade A Minus) (Grade A Plus)) = Lt.
Proof. simpl. reflexivity. Qed.
Example test_grade_comparison3 :
  (grade_comparison (Grade F Plus) (Grade F Plus)) = Eq.
Proof. simpl. reflexivity. Qed.
Example test_grade_comparison4 :
  (grade_comparison (Grade B Minus) (Grade C Plus)) = Gt.
Proof. simpl. reflexivity. Qed.

Definition lower_letter (l : letter) : letter :=
  match l with
  | A => B
  | B => C
  | C => D
  | D => F
  | F => F (* Can't go lower than F! *)
  end.

Theorem lower_letter_lowers:
  forall (l : letter),
    letter_comparison F l = Lt ->
    letter_comparison (lower_letter l) l = Lt.
Proof.
    intros [].
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - intros H.
        simpl.
        rewrite <- H.
        reflexivity.
Qed.

Definition lower_grade (g : grade) : grade :=
  match g with
  | Grade l m =>
    match m with
    | Minus => 
        match l with
        | F => Grade F Minus
        | _ => Grade (lower_letter l) Plus
        end
    | Plus => Grade l Natural
    | Natural => Grade l Minus
    end
end.

Example lower_grade_A_Plus :
  lower_grade (Grade A Plus) = (Grade A Natural).
Proof.
simpl. reflexivity. Qed.
Example lower_grade_A_Natural :
  lower_grade (Grade A Natural) = (Grade A Minus).
Proof.
simpl. reflexivity. Qed.
Example lower_grade_A_Minus :
  lower_grade (Grade A Minus) = (Grade B Plus).
Proof.
simpl. reflexivity. Qed.
Example lower_grade_B_Plus :
  lower_grade (Grade B Plus) = (Grade B Natural).
Proof.
simpl. reflexivity. Qed.
Example lower_grade_F_Natural :
  lower_grade (Grade F Natural) = (Grade F Minus).
Proof.
simpl. reflexivity. Qed.
Example lower_grade_twice :
  lower_grade (lower_grade (Grade B Minus)) = (Grade C Natural).
Proof.
simpl. reflexivity. Qed.
Example lower_grade_thrice :
  lower_grade (lower_grade (lower_grade (Grade B Minus))) = (Grade C Minus).
Proof.
simpl. reflexivity. Qed.

Theorem lower_grade_lowers :
  forall (g : grade),
    grade_comparison (Grade F Minus) g = Lt ->
    grade_comparison (lower_grade g) g = Lt.
Proof.
    intros [].
    destruct l eqn:El.
    - destruct m eqn:Em.
        -- reflexivity.
        -- reflexivity.
        -- reflexivity.
    - destruct m eqn:Em.
        -- reflexivity.
        -- reflexivity.
        -- reflexivity.
    - destruct m eqn:Em.
        -- reflexivity.
        -- reflexivity.
        -- reflexivity.
    - destruct m eqn:Em.
        -- reflexivity.
        -- reflexivity.
        -- reflexivity.
    - destruct m eqn:Em.
        -- reflexivity.
        -- reflexivity.
        -- simpl.
            intros H.
            rewrite H.
            reflexivity.
Qed.
    