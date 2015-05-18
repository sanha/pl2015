Require Export Assignment05_25.

(* problem #26: 10 points *)




(** 3 star (even__ev)  
    Note that proving [even__ev] directly is hard.
    You might find it easier to prove [even__ev_strong] first
    and then prove [even__ev] using it.
*)

Lemma even__ev_strong: forall n : nat, 
  (even (pred n) -> ev (pred n)) /\ (even n -> ev n).
Proof.
  induction n as [| n'].
  - split.
    + intros H. simpl. apply ev_0.
    + intros H. apply ev_0.
  - split.
    + inversion IHn'. intros H1. simpl. simpl in H1. apply H0. apply H1.
    + intros H. inversion IHn'. induction n' as [| n''].
      * unfold even in H. simpl in H. inversion H.
      * apply ev_SS in H0. simpl in H0. apply H0. simpl. unfold even in H. simpl in H. unfold even. apply H.
Qed.
(** [] *)
