Require Export Assignment05_04.

(* problem #05: 10 points *)


(** 1 star, optional (or_distributes_over_and)  *)
Theorem or_distributes_over_and : forall P Q R : Prop,
  P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R).
Proof.
  intros. apply conj.
  - intros H. apply conj.
    + destruct H.
      * apply or_introl. apply H.
      * destruct H. apply or_intror. apply H.
    + destruct H. 
      * apply or_introl. apply H.
      * apply or_intror. apply H.
  - intros H. destruct H. destruct H.
    + apply or_introl. apply H.
    + destruct H0.
      * apply or_introl. apply H0.
      * apply or_intror. apply conj. apply H. apply H0.
Qed.
(** [] *)


