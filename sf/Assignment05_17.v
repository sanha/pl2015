Require Export Assignment05_16.

(* problem #17: 10 points *)



Lemma zero_mult_n: forall n: nat, 0*n = 0.
Proof.
  induction n as [| n'].
  - simpl. reflexivity.
  - simpl. apply IHn'.
Qed.


Lemma m_mult_S: forall m n: nat, (S m) * n = m * n + n.
Proof.
  simpl. induction m as [| m'].
  - simpl. induction n as [| n'].
    + simpl. reflexivity.
    + simpl. rewrite -> IHn'. reflexivity.
  - intros n. rewrite -> plus_comm with (S m' * n) n. reflexivity.
Qed.

(** 3 stars (b_timesm)  *)
Theorem b_timesm: forall n m, beautiful n -> beautiful (m*n).
Proof.
  induction m as [| m'].
  - intros. rewrite -> zero_mult_n. apply b_0.
  - intros. rewrite -> m_mult_S. apply b_sum. apply IHm'. apply H. apply H. 
Qed.
(** [] *)