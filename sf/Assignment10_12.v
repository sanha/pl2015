Require Export Assignment10_11.

(* problem #12: 10 points *)

(** **** Exercise: 3 stars, optional  *)
Lemma par_body_n__Sn : forall n st,
  st X = n /\ st Y = 0 ->
  par_loop / st ==>c* par_loop / (update st X (S n)).
Proof.
  intros. inversion H. unfold par_loop at 1. 
  eapply multi_step. apply CS_Par1.  

constructor. constructor. 


 eapply multi_trans. with (y := (par_loop, st).




 assert (par_loop / st ==>c par_loop / update st X (S n)).
  { constructor.
  }

apply multi_trans with (y := par_loop / st ==>c* par_loop / update st X (S n)).



  exact FILL_IN_HERE.
Qed.

(*-- Check --*)
Check par_body_n__Sn : forall n st,
  st X = n /\ st Y = 0 ->
  par_loop / st ==>c* par_loop / (update st X (S n)).



Theorem par_loop_any_X:
  forall n, exists st',
    par_loop / empty_state ==>*  SKIP / st'
    /\ st' X = n.
Proof.
  intros n. 
  destruct (par_body_n n empty_state). 
    split; unfold update; reflexivity.

  rename x into st.
  inversion H as [H' [HX HY]]; clear H. 
  exists (update st Y 1). split.
  eapply multi_trans with (par_loop,st). apply H'. 
  eapply multi_step. apply CS_Par1. apply CS_Ass.
  eapply multi_step. apply CS_Par2. apply CS_While.
  eapply multi_step. apply CS_Par2. apply CS_IfStep.
    apply BS_Eq1. apply AS_Id. rewrite update_eq.
  eapply multi_step. apply CS_Par2. apply CS_IfStep.
    apply BS_Eq. simpl.
  eapply multi_step. apply CS_Par2. apply CS_IfFalse.
  eapply multi_step. apply CS_ParDone.
  apply multi_refl.

  rewrite update_neq. assumption. intro X; inversion X. 
Qed.

End CImp.