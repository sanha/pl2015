Require Export Assignment08_16.

(* problem #17: 10 points *)

Lemma optimize_0plus_bexp_sound:
  btrans_sound optimize_0plus_bexp.
Proof.
  unfold btrans_sound. unfold bequiv. intros. induction b ; try reflexivity.
  - simpl. assert ((aeval st a) = (aeval st (Assignment08_00.optimize_0plus_aexp a))).
    apply optimize_0plus_aexp_sound.
    assert ((aeval st a0) = (aeval st (Assignment08_00.optimize_0plus_aexp a0))).
    apply optimize_0plus_aexp_sound. rewrite <- H; rewrite <- H0; reflexivity.
  - simpl. assert ((aeval st a) = (aeval st (Assignment08_00.optimize_0plus_aexp a))).
    apply optimize_0plus_aexp_sound.
    assert ((aeval st a0) = (aeval st (Assignment08_00.optimize_0plus_aexp a0))).
    apply optimize_0plus_aexp_sound. rewrite <- H; rewrite <- H0; reflexivity.
  - simpl. rewrite IHb. reflexivity.
  - simpl. rewrite IHb1. rewrite IHb2. reflexivity.
Qed.

(*-- Check --*)
Check optimize_0plus_bexp_sound:
  btrans_sound optimize_0plus_bexp.

