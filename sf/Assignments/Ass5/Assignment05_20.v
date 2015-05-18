Require Export Assignment05_19.

(* problem #20: 10 points *)








(** 3 stars, advanced (beautiful__gorgeous)  *)
Theorem beautiful__gorgeous : forall n, beautiful n -> gorgeous n.
Proof.
  intros. induction H as [ | | | n' m' H0 H1 H2 H3].
  - apply g_0.
  - apply g_plus3. apply g_0.
  - apply g_plus5. apply g_0.
  - apply gorgeous_sum. apply H1. apply H3.
Qed.
(** [] *)




