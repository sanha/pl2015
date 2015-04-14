Require Export Assignment05_05.

(* problem #06: 10 points *)


(** 2 stars, optional (orb_false)  *)
Theorem orb_prop : forall b c,
  orb b c = true -> b = true \/ c = true.
Proof.
  intros b c. destruct b.
  - unfold orb. intros H. apply or_introl. apply H.
  - unfold orb. intros H. apply or_intror. apply H.
Qed.


