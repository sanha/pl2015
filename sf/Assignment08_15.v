Require Export Assignment08_14.

(* problem #15: 10 points *)

Lemma WHILE_true_nonterm : forall b c st st',
     bequiv b BTrue ->
     ~( (WHILE b DO c END) / st || st' ).
Proof. 
  intros b c st st' Hb.
  intros H.
  remember (WHILE b DO c END) as cw eqn:Heqcw.
  ceval_cases (induction H) Case;
    inversion Heqcw; subst; clear Heqcw.
  Case "E_WhileEnd". 
    unfold bequiv in Hb.
    rewrite Hb in H. inversion H.
  Case "E_WhileLoop". 
    apply IHceval2. reflexivity.  Qed.

(** **** Exercise: 3 stars (fold_constants_com_sound)  *)
(** Complete the [WHILE] case of the following proof. *)

Theorem fold_constants_com_sound : 
  ctrans_sound fold_constants_com.
Proof. 
  unfold ctrans_sound. intros c. 
  com_cases (induction c) Case; simpl.
  Case "SKIP". apply refl_cequiv.
  Case "::=". apply CAss_congruence. apply fold_constants_aexp_sound.
  Case ";;". 
    (***
     Note how we use the tactic [eauto].
     ***)
   destruct c1; destruct c2; try (apply CSeq_congruence; assumption)
   ; eauto using skip_left, skip_right.
  Case "IFB". 
    assert (bequiv b (fold_constants_bexp b)).
      SCase "Pf of assertion". apply fold_constants_bexp_sound.
    destruct (fold_constants_bexp b) eqn:Heqb;
      (* If the optimization doesn't eliminate the if, then the result
         is easy to prove from the IH and fold_constants_bexp_sound *)
      try (apply CIf_congruence; assumption).
    SCase "b always true".
      apply trans_cequiv with c1 ; try assumption.
      apply IFB_true; assumption.
    SCase "b always false".
      apply trans_cequiv with c2; try assumption.
      apply IFB_false; assumption.
  Case "WHILE".
    { assert (bequiv b (fold_constants_bexp b)). apply fold_constants_bexp_sound.
      destruct (fold_constants_bexp b) eqn: Hb ; try (apply CWhile_congruence ; assumption).
      - unfold cequiv. split ; intros. 
        + apply WHILE_true_nonterm with b c st st' in H. apply H in H0. inversion H0.
        + apply loop_never_stops in H0. inversion H0.
      - unfold cequiv. split ; intros.
        + inversion H0 ; subst. apply E_Skip. apply WHILE_true_nonterm with b c st'0 st' in H7.
          inversion H7. unfold bequiv in H. simpl in H. rewrite H in H3. inversion H3.
        + inversion H0 ; subst. apply E_WhileEnd. apply H.
    }
Qed.

(*-- Check --*)
Check fold_constants_com_sound : 
  ctrans_sound fold_constants_com.

