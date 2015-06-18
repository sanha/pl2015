Require Export Assignment11_02.

(* problem #03: 10 points *)

(** **** Exercise: 3 stars, optional (step_deterministic)  *)
(** Using [value_is_nf], we can show that the [step] relation is
    also deterministic... *)

Theorem step_deterministic:
  deterministic step.
Proof with eauto.
  unfold deterministic. intros. generalize dependent y2.
  induction H ; intros.
  - inversion H0; subst. reflexivity. inversion H4.
  - inversion H0; subst. reflexivity. inversion H4.
  - inversion H0; subst.
    + inversion H.
    + inversion H.
    + apply IHstep in H5. subst. reflexivity.
  - inversion H0 ; subst. apply IHstep in H2. subst. reflexivity.
  - inversion H0. reflexivity. solve by inversion.
  - inversion H0 ; subst. reflexivity. assert (value t1). eauto. inversion H2 ; subst.
    apply value_is_nf in H1. unfold normal_form in H1. unfold not in H1. 
    assert (exists t':tm, t1 ==> t'). eauto. apply H1 in H3. inversion H3.
  - inversion H0; subst. 
    + solve by inversion.
    + inversion H ; subst. assert (value y2). eauto. apply value_is_nf in H1. unfold normal_form in H1.
      assert (exists t':tm, y2 ==> t'). eauto. apply H1 in H4. inversion H4.
    + inversion H0 ; subst. inversion H3. apply IHstep in H2. subst. reflexivity.
  - inversion H0. reflexivity. inversion H1.
  - inversion H0; subst. reflexivity. inversion H2 ; subst. 
    assert (value t1). eauto. apply value_is_nf in H1. unfold normal_form in H1.
    assert (exists t':tm, t1 ==> t'). eauto. apply H1 in H4. inversion H4.
  - inversion H0; subst.
    + inversion H.
    + inversion H ; subst.  
      assert (value t0). eauto. apply value_is_nf in H1. unfold normal_form in H1.
      assert (exists t':tm, t0 ==> t'). eauto. apply H1 in H4. inversion H4.
    + apply IHstep in H2. subst. reflexivity.
Qed.

(*-- Check --*)
Check step_deterministic:
  deterministic step.