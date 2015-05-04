Require Export Assignment07_01.

(* problem #02: 10 points *)

Fixpoint optimize_1mult (a:aexp) : aexp :=
  match a with
  | ANum n =>
      ANum n
  | APlus e1 e2 =>
      APlus (optimize_1mult e1) (optimize_1mult e2)
  | AMinus e1 e2 =>
      AMinus (optimize_1mult e1) (optimize_1mult e2)
  | AMult (ANum 1) e2 =>
      optimize_1mult e2
  | AMult e1 (ANum 1) =>
      optimize_1mult e1
  | AMult e1 e2 =>
      AMult (optimize_1mult e1) (optimize_1mult e2)
  end.

(** Hint:
    If you use the tacticals [;], [try] and [omega] well,
    you can prove the following theorem in 5 lines.
 **)
Theorem optimize_1mult_sound: forall a,
  aeval (optimize_1mult a) = aeval a.
Proof.
  intros. induction a. auto. simpl. auto. simpl. auto. induction a1.
  - destruct n ; try auto. induction a2 ; try auto.
    + destruct n ; try auto. destruct n ; try auto.
    + destruct n ; auto. simpl. omega.
      induction a2 ; simpl ; auto.
      * destruct n0 ; try auto. destruct n0 ; auto.
        simpl. omega.
  - induction a2 ; simpl ; auto.
    + destruct n ; auto. simpl. omega. destruct n ; auto. simpl. rewrite mult_1_r. auto.
      simpl. auto.
  - induction a2 ; simpl ; auto.
    + destruct n ; auto. simpl. omega. destruct n; auto. simpl. rewrite mult_1_r. auto.
      simpl. auto.
  - induction a2 ; simpl ; auto.
    + destruct n ; auto. simpl. omega. destruct n; auto. simpl. rewrite mult_1_r. auto.
      simpl. auto. 
Qed.