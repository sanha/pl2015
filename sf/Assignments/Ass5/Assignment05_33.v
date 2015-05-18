Require Export Assignment05_32.

(* problem #33: 10 points *)

Theorem le_plus_l : forall a b,
  a <= a + b.
Proof. 
  induction a as [| a'].
  - simpl. apply O_le_n.
  - intros. induction b as [| b'].
    + simpl. rewrite -> plus_comm with a' 0. simpl. apply le_n.
    + simpl. rewrite -> plus_comm with a' (S b'). simpl. apply le_S. rewrite -> plus_comm with b' a'.
      apply n_le_m__Sn_le_Sm. apply IHa'.
Qed.
