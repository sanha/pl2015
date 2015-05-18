Require Export Assignment05_31.

(* problem #32: 10 points *)

Theorem Sn_le_Sm__n_le_m : forall n m,
  S n <= S m -> n <= m.
Proof.
  induction n as [| n'].
  - intros. apply O_le_n.
  - intros. induction m as [| m'].
    + inversion H. inversion H2.
    + inversion H.
      * apply le_n.
      * apply le_S. apply IHm'. apply H2.
Qed.

