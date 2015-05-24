Require Export Assignment08_12.

(* problem #13: 10 points *)

(** **** Exercise: 3 stars (CIf_congruence)  *)
Theorem CIf_congruence : forall b b' c1 c1' c2 c2',
  bequiv b b' -> cequiv c1 c1' -> cequiv c2 c2' ->
  cequiv (IFB b THEN c1 ELSE c2 FI) (IFB b' THEN c1' ELSE c2' FI).
Proof.
  unfold bequiv, cequiv. intros. split ; subst.
  - destruct (beval st b) eqn: H2 ; subst.
    + intros. apply E_IfTrue. rewrite <- H2. symmetry. apply H. inversion H3 ; subst.
      apply H0 in H10. assumption. rewrite H2 in H9. inversion H9.
    + intros. apply E_IfFalse. rewrite <- H2. symmetry. apply H. inversion H3 ; subst.
      rewrite H2 in H9. inversion H9. apply H1 in H10. assumption.
  - destruct (beval st b') eqn: H2; subst.
    + intros. apply E_IfTrue. rewrite <- H2. apply H. inversion H3 ; subst.
      apply H0 in H10. assumption. rewrite H2 in H9. inversion H9.
    + intros. apply E_IfFalse. rewrite <- H2. apply H. inversion H3 ; subst.
      rewrite H2 in H9. inversion H9. apply H1 in H10. assumption.
Qed.

(*-- Check --*)
Check CIf_congruence : forall b b' c1 c1' c2 c2',
  bequiv b b' -> cequiv c1 c1' -> cequiv c2 c2' ->
  cequiv (IFB b THEN c1 ELSE c2 FI) (IFB b' THEN c1' ELSE c2' FI).

