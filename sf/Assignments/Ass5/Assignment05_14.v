Require Export Assignment05_13.

(* problem #14: 10 points *)

(** 2 star (ev__even)  *)
Theorem ev__even: forall n : nat,
  ev n -> even n.
Proof.
  intros n H. unfold even. induction H as [| n' H'].
  - simpl. reflexivity.
  - simpl. apply IHH'.
Qed.
(** [] *)


