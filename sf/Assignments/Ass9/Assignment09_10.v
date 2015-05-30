Require Export Assignment09_09.

(* problem #10: 10 points *)

(** **** Exercise: 3 stars (two_loops)  *)
(** Here is a very inefficient way of adding 3 numbers:
  X ::= 0;;
  Y ::= 0;;
  Z ::= c;;
  WHILE X <> a DO
    X ::= X + 1;;
    Z ::= Z + 1
  END;;
  WHILE Y <> b DO
    Y ::= Y + 1;;
    Z ::= Z + 1
  END

    Show that it does what it should by filling in the blanks in the
    following decorated program.

    {{ True }} ->>
    {{                                        }}
  X ::= 0;;
    {{                                        }}
  Y ::= 0;;
    {{                                        }}
  Z ::= c;;
    {{                                        }}
  WHILE X <> a DO
      {{                                        }} ->>
      {{                                        }}
    X ::= X + 1;;
      {{                                        }}
    Z ::= Z + 1
      {{                                        }}
  END;;
    {{                                        }} ->>
    {{                                        }}
  WHILE Y <> b DO
      {{                                        }} ->>
      {{                                        }}
    Y ::= Y + 1;;
      {{                                        }}
    Z ::= Z + 1
      {{                                        }}
  END
    {{                                        }} ->>
    {{ Z = a + b + c }}
*)

Theorem add_three_numbers_correct: forall a b c,
  {{ fun st => True }}                                   
  X ::= ANum 0;;
  Y ::= ANum 0;;
  Z ::= ANum c;;
  WHILE BNot (BEq (AId X) (ANum a)) DO
    X ::= APlus (AId X) (ANum 1);;
    Z ::= APlus (AId Z) (ANum 1)
  END;;
  WHILE BNot (BEq (AId Y) (ANum b)) DO
    Y ::= APlus (AId Y) (ANum 1);;
    Z ::= APlus (AId Z) (ANum 1)
  END
  {{ fun st => st Z = a + b + c }}.
Proof.
  intros. apply hoare_seq with (Q := fun st : state => st X = 0).
  apply hoare_seq with (Q := fun st : state => st X = 0 /\ st Y = 0).
  apply hoare_seq with (Q := fun st : state => st X = 0 /\ st Y = 0 /\ st Z = c).
  apply hoare_seq with (Q := fun st : state => st X = a /\ st Y = 0 /\ st Z = a + c).
  { apply hoare_consequence_post with (fun st : state => st Z = st Y + a + c /\ beval st (BNot (BEq (AId Y) (ANum b))) = false).
    apply hoare_consequence_pre with (fun st: state => st Z = st Y + a + c).
    - apply hoare_while. simpl. eapply hoare_seq. apply hoare_asgn.
      unfold assn_sub. simpl. unfold hoare_triple. intros. inversion H ; subst. simpl.
      unfold update. simpl. omega.
    - unfold assert_implies. intros. omega.
    - unfold assert_implies. intros. inversion H ; subst. simpl in H1. unfold negb in H1. 
      destruct (beq_nat (st Y) b) eqn: H'.
      + apply beq_nat_true in H'. rewrite H' in H0. omega.
      + inversion H1.
  } 
  { apply hoare_consequence_post with (fun st: state => (st Y = 0 /\ st Z = st X + c) /\ beval st (BNot (BEq (AId X) (ANum a))) = false).
    apply hoare_consequence_pre with (fun st: state => st Y = 0 /\ st Z = st X + c).
    - apply hoare_while. simpl. eapply hoare_seq. apply hoare_asgn.
      unfold assn_sub. simpl. unfold hoare_triple. intros. inversion H ; subst. simpl.
      unfold update. simpl. omega.
    - unfold assert_implies. intros. omega.
    - unfold assert_implies. intros. inversion H ; subst. inversion H0 ; subst. simpl in H1. unfold negb in H1. 
      destruct (beq_nat (st X) a) eqn: H'.
      + apply beq_nat_true in H'. rewrite H' in H0. omega.
      + inversion H1.
  }
  - unfold hoare_triple. intros. constructor.
    + inversion H0. inversion H ; subst. simpl. unfold update. auto.
    + constructor.
      * inversion H0. inversion H ; subst. simpl. unfold update. auto.
      * inversion H0. inversion H ; subst. simpl. unfold update. auto.
  - unfold hoare_triple. intros. constructor.
    + inversion H ; subst. simpl. unfold update. auto.
    + inversion H ; subst. simpl. unfold update. auto.
  - unfold hoare_triple. intros. inversion H ; subst. unfold update. auto.
Qed.

(*-- Check --*)
Check add_three_numbers_correct: forall a b c,
  {{ fun st => True }}                                   
  X ::= ANum 0;;
  Y ::= ANum 0;;
  Z ::= ANum c;;
  WHILE BNot (BEq (AId X) (ANum a)) DO
    X ::= APlus (AId X) (ANum 1);;
    Z ::= APlus (AId Z) (ANum 1)
  END;;
  WHILE BNot (BEq (AId Y) (ANum b)) DO
    Y ::= APlus (AId Y) (ANum 1);;
    Z ::= APlus (AId Z) (ANum 1)
  END
  {{ fun st => st Z = a + b + c }}.

