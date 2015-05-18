Require Export Assignment05_33.

(* problem #34: 10 points *)

Theorem plus_lt : forall n1 n2 m,
  n1 + n2 < m ->
  n1 < m /\ n2 < m.
Proof. 
  unfold lt. induction n1 as [| n'].
  - induction n2 as [| m'].
    + intros. split. simpl in H. apply H. simpl in H. apply H.
    + intros. split. simpl in H. induction m as [| m''].
      * inversion H.
      * apply n_le_m__Sn_le_Sm. apply O_le_n.
      * simpl in H. apply H.
  - induction n2 as [| m'].
    + intros. split. rewrite -> plus_comm with (S n') 0 in H. simpl in H. apply H.
      rewrite -> plus_comm with (S n') 0 in H. simpl in H. inversion H. apply n_le_m__Sn_le_Sm. apply O_le_n.
      apply n_le_m__Sn_le_Sm. apply O_le_n.
    + intros. split. 
      * apply IHm'. apply le_S in H. apply Sn_le_Sm__n_le_m in H. simpl in H. rewrite -> plus_comm with n' (S m') in H.
        simpl in H. rewrite -> plus_comm with m' n' in H. simpl. apply H.
      * apply IHn'. apply le_S in H. apply Sn_le_Sm__n_le_m in H. simpl in H. apply H.
Qed.

