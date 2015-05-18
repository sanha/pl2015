Require Export Assignment05_11.

(* problem #12: 10 points *)

Lemma ineq_prop : forall n m : nat, (S n = S m -> False) -> (n = m -> False). 
Proof.
  induction n as [| n'].
  - induction m as [| n'].
    + intros contra. destruct contra. reflexivity.
    + intros contra. intros H. inversion H.
  - induction m as [| m'].
    + intros H. intros H1. inversion H1. 
    + intros H. intros H0. inversion H0. rewrite -> H0 in H. apply H. reflexivity.

Qed.

(** 2 stars (false_beq_nat)  *)
Theorem false_beq_nat : forall n m : nat,
     n <> m ->
     beq_nat n m = false.
Proof.
  unfold not. induction n as [| n'].
  - induction m as [| m'].
    + intros H. destruct H. reflexivity.
    + intros H. simpl. reflexivity.
  - induction m as [| m'].
    + simpl. reflexivity.
    + intros H. apply IHn'. apply ineq_prop. apply H.
Qed.
(** [] *)





