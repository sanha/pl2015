Require Export Assignment05_08.

(* problem #09: 10 points *)



(** 2 stars (contrapositive)  *)
Theorem contrapositive : forall P Q : Prop,
  (P -> Q) -> (~Q -> ~P).
Proof.
  intros. unfold not. unfold not in H0. intros H1. apply H0 in H. apply H. apply H1.
Qed.
(** [] *)



