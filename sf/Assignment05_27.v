Require Export Assignment05_26.

(* problem #27: 10 points *)


Theorem even__ev: forall n : nat,
  even n -> ev n.
Proof.
  induction n as [| n'].
  - intros H. apply ev_0.
  - intros H. apply even__ev_strong. apply H.
Qed.
(** [] *)


