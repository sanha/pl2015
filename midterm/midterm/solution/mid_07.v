Require Export mid_06.

(* problem #07: 10 points *)

(** Hard:
    Prove the following theorem.
 **)

Lemma two_three_rel_prime: forall n m
    (EQ: 2 * n = 3 * m),
  exists k, m = 2 * k.
Proof.
  intros.
  destruct (odd_or_even m) as [k [EQK | EQK]]; subst.
  (* { exists k; auto. }
  exfalso.
  assert (exists l, 3 = 2 * l). *)
  - exists k; auto.
  - rewrite mult_plus_distr_l in EQ.
    rewrite mult_assoc in EQ.
    rewrite (mult_comm 3 2) in EQ.
    rewrite plus_comm in EQ.
    rewrite <- mult_assoc in EQ.
    apply plus_minus in EQ.
    rewrite <- mult_minus_distr_l in EQ.
    destruct (n-3*k); inversion EQ.
    destruct n0; [inversion H0|].
    destruct n0; [inversion H0|].
    destruct n0; [inversion H0|].
    inversion H0.
Qed.

