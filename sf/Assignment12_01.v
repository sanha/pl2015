Require Export Assignment12_00.

(* problem #01: 10 points *)

(** **** Exercise: 3 stars, optional (typing_nonexample_3)  *)
(** Another nonexample:
    ~ (exists S, exists T,
          empty |- \x:S. x x : T).
*)

Lemma uniqueness: ~ (exists t1 t2:ty, t1 = (TArrow t1 t2)).
    intros contra. inversion contra. induction x; intros ; try (inversion H; inversion H0).
    - assert (exists t2: ty, x1 = TArrow x1 t2).
      exists x2. assumption. apply IHx1 in H1. inversion H1.
Qed.  

Example typing_nonexample_3 :
  ~ (exists S, exists T,
        empty |- 
          (tabs X S
             (tapp (tvar X) (tvar X))) \in
          T).
Proof.
  intros contra. inversion contra. inversion H.
  inversion H0 ; subst. inversion H6 ; subst.
  inversion H4 ; subst. rewrite extend_eq in H3.
  inversion H7 ; subst. rewrite extend_eq in H5.
  inversion H3. inversion H5. rewrite H8 in H2.
  assert (exists t1 t2: ty, t1 = TArrow t1 t2). exists T1. exists T12. assumption.
  apply uniqueness in H1. inversion H1.
Qed.

(*-- Check --*)
Check typing_nonexample_3 :
  ~ (exists S, exists T,
        empty |- 
          (tabs X S
             (tapp (tvar X) (tvar X))) \in
          T).

