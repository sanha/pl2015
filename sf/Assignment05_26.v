Require Export Assignment05_25.

(* problem #26: 10 points *)



Lemma pred_n: forall n : nat, S n = S (S (pred n)).
Proof.
  intros. induction n as [| n']. 
  - simpl.
Qed.







(** 3 star (even__ev)  
    Note that proving [even__ev] directly is hard.
    You might find it easier to prove [even__ev_strong] first
    and then prove [even__ev] using it.
*)

Lemma even__ev_strong: forall n : nat, 
  (even (pred n) -> ev (pred n)) /\ (even n -> ev n).
Proof.
  intros. induction n as [| n'].
  - split.
    + intros H. simpl. apply ev_0.
    + intros H. apply ev_0.
  - inversion IHn'. split.
    + intros H1. simpl. simpl in H1. apply H0. apply H1.
    + intros H1. 
Qed.
(** [] *)



