Require Export Assignment10_12.

(* problem #13: 10 points *)

(** **** Exercise: 3 stars, optional  *)
Lemma par_body_n : forall n st,
  st X = 0 /\ st Y = 0 ->
  exists st',
    par_loop / st ==>c*  par_loop / st' /\ st' X = n /\ st' Y = 0.
Proof.
  intros. induction n.
  { exists st. split. constructor. assumption. }
  { inversion IHn. inversion H0. apply par_body_n__Sn in H2.
    exists (update x X (S n)). split.
    apply multi_trans with (y := (par_loop, x)) ; assumption.
    split. compute. reflexivity. inversion H0. inversion H4.
    unfold update. destruct (eq_id_dec X Y). solve by inversion. assumption.
  } 
Qed.

(*-- Check --*)
Check par_body_n : forall n st,
  st X = 0 /\ st Y = 0 ->
  exists st',
    par_loop / st ==>c*  par_loop / st' /\ st' X = n /\ st' Y = 0.

