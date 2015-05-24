Require Export Assignment08_17.

(* problem #18: 10 points *)

Lemma optimize_0plus_com_sound:
  ctrans_sound optimize_0plus_com.
Proof.
  unfold ctrans_sound. unfold cequiv. induction c.
  - reflexivity.
  - simpl. apply CAss_congruence. apply optimize_0plus_aexp_sound.
  - simpl. apply CSeq_congruence ; unfold cequiv. apply IHc1. apply IHc2.
  - simpl. apply CIf_congruence ; try unfold cequiv. apply optimize_0plus_bexp_sound. 
    apply IHc1. apply IHc2.
  - simpl. apply CWhile_congruence. apply optimize_0plus_bexp_sound. unfold cequiv. apply IHc.
Qed.

(*-- Check --*)
Check optimize_0plus_com_sound:
  ctrans_sound optimize_0plus_com.

