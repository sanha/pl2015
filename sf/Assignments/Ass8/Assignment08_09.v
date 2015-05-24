Require Export Assignment08_08.

(* problem #09: 10 points *)

(** **** Exercise: 2 stars (WHILE_true)  *)
(** Prove the following theorem. _Hint_: You'll want to use
    [WHILE_true_nonterm] here. *)

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


Theorem WHILE_true: forall b c,
     bequiv b BTrue  ->
     cequiv 
       (WHILE b DO c END)
       (WHILE BTrue DO SKIP END).
Proof. 
  split ; intros. 
  - apply WHILE_true_nonterm in H0. inversion H0. assumption.
  - assert ((WHILE BTrue DO SKIP END) = loop). unfold loop. reflexivity.
    rewrite H1 in H0. apply loop_never_stops in H0. inversion H0.
Qed.

(*-- Check --*)
Check WHILE_true: forall b c,
     bequiv b BTrue  ->
     cequiv 
       (WHILE b DO c END)
       (WHILE BTrue DO SKIP END).

