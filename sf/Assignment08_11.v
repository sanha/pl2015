Require Export Assignment08_10.

(* problem #11: 10 points *)

Definition beq_id (X1 : id) (X2 : id) : bool :=
  match (X1, X2) with
    (Id x1, Id x2) => beq_nat x1 x2
  end.

Theorem update_same : forall n1 x1 x2 (st : state),
  st x1 = n1 ->
  (update st x1 n1) x2 = st x2.
Proof.
  intros. unfold update. remember (beq_id x1 x2). destruct b.
  - destruct (eq_id_dec x1 x2). subst. reflexivity. reflexivity.
  - destruct (eq_id_dec x1 x2). subst. reflexivity. reflexivity.
Qed.

(** **** Exercise: 2 stars (assign_aequiv)  *)
Theorem assign_aequiv : forall X e,
  aequiv (AId X) e -> 
  cequiv SKIP (X ::= e).
Proof.
  intros. split ; intros.
  - inversion H0 ; subst. assert ((update st' X (aeval st' e)) = st').
    + unfold aequiv in H. rewrite <- H. simpl. apply functional_extensionality. intros. 
      apply update_same. reflexivity.
    + rewrite <- H1 at 2. apply E_Ass. reflexivity.
  - inversion H0 ; subst. assert ((update st X (aeval st e)) = st).
    + unfold aequiv in H. simpl in H. rewrite <- H. apply functional_extensionality. intros. 
      apply update_same. reflexivity.
    + rewrite H1. apply E_Skip.
Qed.

(*-- Check --*)
Check assign_aequiv : forall X e,
  aequiv (AId X) e -> 
  cequiv SKIP (X ::= e).

