Require Export Assignment05_36.

(* problem #37: 10 points *)

Theorem le_ble_nat : forall n m,
  n <= m ->
  ble_nat n m = true.
Proof.
  induction n as [| n'].
  - intros. simpl. reflexivity.
  - intros. induction m as [| m'].
    + inversion H.
    + simpl. apply IHn'. apply Sn_le_Sm__n_le_m in H. apply H.
Qed.

