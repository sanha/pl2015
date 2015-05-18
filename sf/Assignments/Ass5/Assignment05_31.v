Require Export Assignment05_30.

(* problem #31: 10 points *)

Theorem n_le_m__Sn_le_Sm : forall n m,
  n <= m -> S n <= S m.
Proof.
  induction n as [| n'].
  - intros. induction m as [| m'].
    + apply le_n.
    + inversion H. apply le_S. apply IHm'. apply H2.
  - intros. induction m as [| m'].
    + inversion H.
    + inversion H.
      * apply le_n.
      * apply le_S. apply IHm'. apply H2.
Qed.

