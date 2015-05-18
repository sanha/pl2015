Require Export Assignment05_09.

(* problem #10: 10 points *)


(** 1 star (not_both_true_and_false)  *)
Theorem not_both_true_and_false : forall P : Prop,
  ~ (P /\ ~P).
Proof. 
  unfold not. intros P contra. inversion contra. apply H0. apply H.
Qed.
(** [] *)



