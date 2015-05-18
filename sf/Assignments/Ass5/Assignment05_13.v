Require Export Assignment05_12.

(* problem #13: 10 points *)



(** 2 stars, optional (beq_nat_false)  *)
Theorem beq_nat_false : forall n m,
  beq_nat n m = false -> n <> m.
Proof.
  unfold not. induction n as [| n'].
  - induction m as [| m']. 
    + intros H. inversion H.
    + intros H. intros H0. rewrite <- H0 in H. inversion H.
  - induction m as [| m'].
    + intros H. intros H0. rewrite -> H0 in H. inversion H.
    + intros H. intros H0. rewrite -> H0 in H. inversion H. inversion H0. destruct IHn' with m'.
      * rewrite -> H3. apply H2.
      *  apply H3.
Qed.
(** [] *)




