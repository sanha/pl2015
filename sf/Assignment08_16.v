Require Export Assignment08_15.


Lemma opt_0plus_l: forall c, optimize_0plus_aexp (APlus (ANum 0) c) = optimize_0plus_aexp c.
Proof. reflexivity. Qed.
Lemma opt_0plus_r: forall c, optimize_0plus_aexp (APlus c (ANum 0)) = optimize_0plus_aexp c.
Proof. destruct c ; try reflexivity. destruct n ; reflexivity. Qed.
Lemma aeval_opt_r : forall c1 c2 st, aeval st c2 = aeval st (optimize_0plus_aexp c2) -> aeval st (APlus c1 c2) = aeval st (APlus c1 (optimize_0plus_aexp c2)).
Proof. intros. simpl. omega. Qed.
Lemma aeval_opt_l : forall c1 c2 st, aeval st c1 = aeval st (optimize_0plus_aexp c1) -> aeval st (APlus c1 c2) = aeval st (APlus (optimize_0plus_aexp c1) c2).
Proof. intros. simpl. omega. Qed.

(* problem #16: 10 points *)
Lemma optimize_0plus_aexp_sound:
  atrans_sound optimize_0plus_aexp.
Proof.
  unfold atrans_sound. unfold aequiv. intros. induction a ; try reflexivity.
  { destruct a1; destruct a2; try (unfold aeval ; unfold aeval in IHa1; unfold aeval in IHa2;
    rewrite -> IHa1; rewrite -> IHa2; reflexivity).
    - unfold aeval at 1. unfold aeval at 1 in IHa1. unfold aeval at 1 in IHa2. destruct n.
      + reflexivity.
      + destruct n0 ; simpl ; omega.
    - unfold aeval at 1. unfold aeval at 1 in IHa1. unfold aeval at 1 in IHa2. destruct n ; reflexivity.
    - unfold aeval at 1 in IHa1. destruct n.
      + rewrite opt_0plus_l. simpl aeval at 1. rewrite <- IHa2. reflexivity.
      + assert (optimize_0plus_aexp (APlus (ANum (S n)) (APlus a2_1 a2_2)) = APlus (ANum (S n)) (optimize_0plus_aexp (APlus a2_1 a2_2))).
        reflexivity. rewrite H. apply aeval_opt_r. assumption. 
    - unfold aeval at 1 in IHa1. destruct n.
      + rewrite opt_0plus_l. simpl aeval at 1. rewrite <- IHa2. reflexivity.
      + assert (optimize_0plus_aexp (APlus (ANum (S n)) (AMinus a2_1 a2_2)) = APlus (ANum (S n)) (optimize_0plus_aexp (AMinus a2_1 a2_2))).
        reflexivity. rewrite H. apply aeval_opt_r. assumption.
    - unfold aeval at 1 in IHa1. destruct n.
      + rewrite opt_0plus_l. simpl aeval at 1. rewrite <- IHa2. reflexivity.
      + assert (optimize_0plus_aexp (APlus (ANum (S n)) (AMult a2_1 a2_2)) = APlus (ANum (S n)) (optimize_0plus_aexp (AMult a2_1 a2_2))).
        reflexivity. rewrite H. apply aeval_opt_r. assumption.
    - unfold aeval at 1. unfold aeval at 1 in IHa1. unfold aeval at 1 in IHa2. destruct n ; simpl ; omega.
    - unfold aeval at 1 in IHa2. destruct n.
      + rewrite opt_0plus_r. simpl aeval at 1. rewrite <- IHa1. simpl. omega.
      + assert (optimize_0plus_aexp (APlus (APlus a1_1 a1_2) (ANum (S n))) = APlus ((optimize_0plus_aexp (APlus a1_1 a1_2))) (ANum (S n))).
        reflexivity. rewrite H. apply aeval_opt_l. assumption.
    - unfold aeval at 1 in IHa2. destruct n.
      + rewrite opt_0plus_r. simpl aeval at 1. rewrite <- IHa1. simpl. omega.
      + assert (optimize_0plus_aexp (APlus (AMinus a1_1 a1_2) (ANum (S n))) = APlus ((optimize_0plus_aexp (AMinus a1_1 a1_2))) (ANum (S n))).
        reflexivity. rewrite H. apply aeval_opt_l. assumption.
    - unfold aeval at 1 in IHa2. destruct n.
      + rewrite opt_0plus_r. simpl aeval at 1. rewrite <- IHa1. simpl. omega.
      + assert (optimize_0plus_aexp (APlus (AMult a1_1 a1_2) (ANum (S n))) = APlus ((optimize_0plus_aexp (AMult a1_1 a1_2))) (ANum (S n))).
        reflexivity. rewrite H. apply aeval_opt_l. assumption.
  }
  { destruct a1; destruct a2; try (unfold aeval ; unfold aeval in IHa1; unfold aeval in IHa2;
    rewrite -> IHa1; rewrite -> IHa2; reflexivity).
  } 
  { destruct a1; destruct a2; try (unfold aeval ; unfold aeval in IHa1; unfold aeval in IHa2;
    rewrite -> IHa1; rewrite -> IHa2; reflexivity).
  } 
Qed.

(*-- Check --*)
Check optimize_0plus_aexp_sound:
  atrans_sound optimize_0plus_aexp.




