Require Export Assignment09_05.

(* problem #06: 10 points *)

(** **** Exercise: 2 stars (slow_assignment)  *)
(** A roundabout way of assigning a number currently stored in [X] to
    the variable [Y] is to start [Y] at [0], then decrement [X] until
    it hits [0], incrementing [Y] at each step. Here is a program that
    implements this idea:
      {{ X = m }}
    Y ::= 0;;
    WHILE X <> 0 DO
      X ::= X - 1;;
      Y ::= Y + 1
    END
      {{ Y = m }} 
    Write an informal decorated program showing that this is correct. *)

Theorem slow_assignment : forall m,
    {{ fun st => st X = m }}
    Y ::= ANum 0;;
    WHILE BNot (BEq (AId X) (ANum 0)) DO
      X ::= AMinus (AId X) (ANum 1);;
      Y ::= APlus (AId Y) (ANum 1)
    END
    {{ fun st => st Y = m }}.
Proof.
  intros m. apply hoare_consequence_post with (Q' := fun st : state => st X + st Y = m /\ beval st (BNot (BEq (AId X) (ANum 0))) = false).
  eapply hoare_seq.
  apply hoare_while with (b := BNot (BEq (AId X) (ANum 0))) (c := X ::= AMinus (AId X) (ANum 1);; Y ::= APlus (AId Y) (ANum 1)).
  - simpl. eapply hoare_seq.
    + apply hoare_asgn.
    + unfold assn_sub. unfold update. simpl. unfold hoare_triple.
      intros. inversion H ; subst. simpl. inversion H0. rewrite <- H1. unfold update. simpl.
      destruct (st X). inversion H2. simpl. omega.
  - unfold hoare_triple. intros. inversion H ; subst. unfold update. simpl. omega.
  - simpl. unfold assert_implies. intros. inversion H. destruct (st X). assumption. inversion H1.
Qed.

(*-- Check --*)
Check slow_assignment : forall m,
    {{ fun st => st X = m }}
    Y ::= ANum 0;;
    WHILE BNot (BEq (AId X) (ANum 0)) DO
      X ::= AMinus (AId X) (ANum 1);;
      Y ::= APlus (AId Y) (ANum 1)
    END
    {{ fun st => st Y = m }}.
  
