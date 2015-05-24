Require Export Assignment08_18.

(* problem #19: 10 points *)

Lemma constfold_0plus_sound:
  ctrans_sound constfold_0plus.
Proof.
  unfold ctrans_sound. unfold constfold_0plus. intros. unfold cequiv. split ; intros.
  - assert (cequiv c (fold_constants_com c)). apply fold_constants_com_sound. unfold cequiv in H0.
    apply H0 in H. assert (cequiv (fold_constants_com c) (optimize_0plus_com (fold_constants_com c))).
    apply optimize_0plus_com_sound. unfold cequiv in H1. apply H1 in H. assumption.
  - assert (cequiv (fold_constants_com c) (optimize_0plus_com (fold_constants_com c))).
    apply optimize_0plus_com_sound. unfold cequiv in H0. apply H0 in H. 
    assert (cequiv c (fold_constants_com c)). apply fold_constants_com_sound. unfold cequiv in H1.
    apply H1 in H. assumption.
Qed.

(*-- Check --*)
Check constfold_0plus_sound:
  ctrans_sound constfold_0plus.

