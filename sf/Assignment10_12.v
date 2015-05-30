Require Export Assignment10_11.

(* problem #12: 10 points *)

(** **** Exercise: 3 stars, optional  *)
Lemma par_body_n__Sn : forall n st,
  st X = n /\ st Y = 0 ->
  par_loop / st ==>c* par_loop / (update st X (S n)).
Proof.
  intros. inversion H. unfold par_loop at 1. subst. 
  eapply multi_step. apply CS_Par2. constructor. 
  eapply multi_step. apply CS_Par2. repeat constructor.
  eapply multi_step. apply CS_Par2. repeat constructor.
  eapply multi_step. apply CS_Par2. rewrite H1. constructor.
  eapply multi_step. apply CS_Par2. repeat constructor.
  eapply multi_step. apply CS_Par2. repeat constructor.
  eapply multi_step. apply CS_Par2. apply CS_SeqStep. apply CS_Ass.
  eapply multi_step. apply CS_Par2. apply CS_SeqFinish.
  rewrite plus_comm. simpl. unfold par_loop. apply multi_refl.
Qed.

(*-- Check --*)
Check par_body_n__Sn : forall n st,
  st X = n /\ st Y = 0 ->
  par_loop / st ==>c* par_loop / (update st X (S n)).
