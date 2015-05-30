Require Export Assignment09_06.

(* problem #07: 10 points *)

(** **** Exercise: 3 stars, optional (add_slowly_decoration)  *)
(** The following program adds the variable X into the variable Z
    by repeatedly decrementing X and incrementing Z.
  WHILE X <> 0 DO
     Z ::= Z + 1;;
     X ::= X - 1
  END

    Following the pattern of the [subtract_slowly] example above, pick
    a precondition and postcondition that give an appropriate
    specification of [add_slowly]; then (informally) decorate the
    program accordingly. *)

Theorem slow_addition_dec_correct : forall n m,
  {{fun st => st X = n /\ st Y = m }}
  WHILE BNot (BEq (AId X) (ANum 0)) DO
     Y ::= APlus (AId Y) (ANum 1);;
     X ::= AMinus (AId X) (ANum 1)
  END
  {{fun st => st Y = n + m}}.
Proof.
  intros. apply hoare_consequence_post with (Q' := fun st : state => st X + st Y = n + m /\ beval st (BNot (BEq (AId X) (ANum 0))) = false).
  - apply hoare_consequence_pre with (P' := fun st : state => st X + st Y = n + m ).
    apply hoare_while with (b := BNot (BEq (AId X) (ANum 0))) (c := Y ::= APlus (AId Y) (ANum 1);; X ::= AMinus (AId X) (ANum 1)).
    simpl. eapply hoare_seq.
    + eapply hoare_asgn.
    + unfold assn_sub. unfold update. simpl. unfold hoare_triple.
      intros. inversion H ; subst. simpl. inversion H0. rewrite <- H1. unfold update. simpl. 
      destruct (st X). inversion H2. omega.
    + unfold assert_implies. intros. inversion H ; subst. auto.
  - unfold assert_implies. intros. inversion H ; subst. inversion H1. destruct (st X). simpl H0. apply H0. inversion H3.
Qed.

(*-- Check --*)
Check slow_addition_dec_correct : forall n m,
  {{fun st => st X = n /\ st Y = m }}
  WHILE BNot (BEq (AId X) (ANum 0)) DO
     Y ::= APlus (AId Y) (ANum 1);;
     X ::= AMinus (AId X) (ANum 1)
  END
  {{fun st => st Y = n + m}}.

