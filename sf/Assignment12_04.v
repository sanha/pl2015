Require Export Assignment12_03.

(* problem #04: 10 points *)

Corollary soundness : forall t t' T,
  empty |- t \in T -> 
  t ==>* t' ->
  ~(stuck t').
Proof.
  intros. intros contra. unfold stuck in contra. unfold normal_form in contra.
  inversion contra. unfold not in H1. unfold not in H2. induction H0.
  - apply progress in H. inversion H. auto. auto. 
  - apply preservation with (t' := y) in H. apply IHmulti in H ; try auto.
    assumption.
Qed.

(*-- Check --*)
Check soundness : forall t t' T,
  empty |- t \in T -> 
  t ==>* t' ->
  ~(stuck t').
