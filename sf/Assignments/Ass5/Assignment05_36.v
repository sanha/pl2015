Require Export Assignment05_35.

(* problem #36: 10 points *)

Theorem ble_nat_true : forall n m,
  ble_nat n m = true -> n <= m.
Proof.
  induction n as [| n'].
  - intros. apply O_le_n.
  - intros. induction m as [| m'].
    + inversion H.
    + apply n_le_m__Sn_le_Sm. apply IHn'. inversion H. reflexivity.
Qed.

