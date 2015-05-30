Require Export Assignment09_08.

(* problem #09: 10 points *)

(** **** Exercise: 4 stars (factorial)  *)
(** Recall that [n!] denotes the factorial of [n] (i.e. [n! =
    1*2*...*n]).  Here is an Imp program that calculates the factorial
    of the number initially stored in the variable [X] and puts it in
    the variable [Y]:
    {{ X = m }} 
  Y ::= 1 ;;
  WHILE X <> 0
  DO
     Y ::= Y * X ;;
     X ::= X - 1
  END
    {{ Y = m! }}

    Fill in the blanks in following decorated program:
    {{ X = m }} ->>
    {{                                      }}
  Y ::= 1;;
    {{                                      }}
  WHILE X <> 0
  DO   {{                                      }} ->>
       {{                                      }}
     Y ::= Y * X;;
       {{                                      }}
     X ::= X - 1
       {{                                      }}
  END
    {{                                      }} ->>
    {{ Y = m! }}
*)

Print fact.

Theorem factorial_dec_correct: forall m,
  {{ fun st => st X = m }} 
  Y ::= ANum 1 ;;
  WHILE BNot (BEq (AId X) (ANum 0))
  DO
     Y ::= AMult (AId Y) (AId X) ;;
     X ::= AMinus (AId X) (ANum 1)
  END
  {{ fun st => st Y = fact m }}.
Proof.
  intros. apply hoare_seq with (Q := fun st : state => st X = m /\ st Y = 1).
  apply hoare_consequence_post with (fun st : state => (st Y) * (fact (st X)) = fact m /\ beval st (BNot (BEq (AId X) (ANum 0))) = false).
  apply hoare_consequence_pre with (P' := fun st : state => (st Y) * (fact (st X)) = fact  m).
  - apply hoare_while. simpl. eapply hoare_seq.
    + apply hoare_asgn.
    + unfold assn_sub. simpl. unfold hoare_triple. intros. unfold update. simpl.
      inversion H0. inversion H ; subst. simpl. unfold update. simpl. destruct (st X).
      * inversion H2.
      * simpl. rewrite <- H1. assert (forall n, n - 0 = n).
        { destruct n0 ; reflexivity. } rewrite H3.
        assert (S n * fact n = fact (S n)).
        { induction n ; auto. } rewrite <- mult_assoc. rewrite H4. reflexivity.
  - unfold assert_implies. intros. inversion H ; subst. rewrite H1. simpl. omega.
  - unfold assert_implies. intros. inversion H ; subst. rewrite <- H0. simpl in H1.
    destruct (st X). simpl. omega. inversion H1.
  - unfold hoare_triple. intros. constructor.
    + inversion H ; subst. unfold update. auto.
    + inversion H ; subst. unfold update. auto.
Qed.

(*-- Check --*)
Check factorial_dec_correct: forall m,
  {{ fun st => st X = m }} 
  Y ::= ANum 1 ;;
  WHILE BNot (BEq (AId X) (ANum 0))
  DO
     Y ::= AMult (AId Y) (AId X) ;;
     X ::= AMinus (AId X) (ANum 1)
  END
  {{ fun st => st Y = fact m }}.

