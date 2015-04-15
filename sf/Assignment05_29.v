Require Export Assignment05_28.

(* problem #29: 10 points *)


Lemma le_zero : forall n:nat, 0 <= n.
Proof.
  induction n as [| n'].
  - apply le_n.
  - apply le_S. apply IHn'.
Qed.

Lemma le_S_S : forall n m: nat, S n <= S m -> n <= m.
Proof.
  induction n as [| n'].
  - induction m as [| m'].
    + intros. apply le_n.
    + intros. apply le_S.
Qed.

Lemma le_Sl : forall n m: nat, S n <= m -> n <= m.
Proof.
  induction n as [| n'].
  - intros. apply le_zero.
  - intros. induction m as [| m'].
    + inversion H.
    + apply le_S in H. simpl in H.
Qed.



(** 2 stars, optional (le_exercises)  *)
(** Here are a number of facts about the [<=] and [<] relations that
    we are going to need later in the course.  The proofs make good
    practice exercises. *)

Lemma le_trans : forall m n o, m <= n -> n <= o -> m <= o.
Proof.
  induction m as [| m'].
  - induction n as [| n'].
    + intros. apply H0.
    + intros. apply le_zero.
  - induction n as [| n'].
    + intros. inversion H.
    + intros. inversion H. apply H0.
 apply IHn'.
Qed.
