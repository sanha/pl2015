Require Export Assignment08_15.

(* problem #16: 10 points *)
Lemma optimize_0plus_aexp_sound:
  atrans_sound optimize_0plus_aexp.
Proof.
(*
  unfold atrans_sound. unfold aequiv. intros. induction a ; try reflexivity.
  - remember (optimize_0plus_aexp a1) as A1. remember (optimize_0plus_aexp a2) as A2. destruct A1.
    + destruct A2.
      { destruct n eqn: H.
        - simpl in IHa1. simpl in IHa2. simpl optimize_0plus_aexp. rewrite <- HeqA1. rewrite <- HeqA2. destruct a1.
          + simpl in IHa1. rewrite IHa1. simpl. omega.
          + simpl. simpl in IHa1. destruct n0 eqn: H0.
            * destruct a2 ; try (simpl ; inversion IHa2 ; omega). inversion HeqA2. simpl. omega.
            * destruct a2 ; try (simpl ; inversion IHa2 ; rewrite H2 ; omega). inversion HeqA2. simpl. omega.
          + simpl. simpl in IHa1. rewrite IHa1. destruct a2 ; try (simpl ; simpl in IHa2 ; assumption).
            * inversion HeqA2. destruct n1 ; reflexivity.
          + simpl. simpl in IHa1. rewrite IHa1. destruct a2 ; try (simpl ; simpl in IHa2 ; assumption).
            * inversion HeqA2. destruct n1 ; reflexivity.
          + simpl. simpl in IHa1. rewrite IHa1. destruct a2 ; try (simpl ; simpl in IHa2 ; assumption).
            * inversion HeqA2. destruct n1 ; reflexivity.
        - { destruct n0 eqn: H0.
            - simpl in IHa1. simpl in IHa2. simpl optimize_0plus_aexp. rewrite <-HeqA1. rewrite <- HeqA2. 
              destruct a1 ; try (simpl in IHa1; destruct a2 ; simpl ; simpl in IHa2 ; rewrite IHa2; simpl ; omega).
              + simpl in IHa1. rewrite IHa1. destruct a2 ; simpl; simpl in IHa2; rewrite IHa2; simpl; omega.
            - simpl in IHa1. simpl in IHa2. simpl optimize_0plus_aexp. rewrite <- HeqA1. rewrite <-HeqA2.
              destruct a1 ; try (simpl in IHa1; destruct a2 ; simpl; simpl in IHa2; rewrite IHa2; simpl; omega).
              + simpl in IHa1. rewrite IHa1. destruct a2 ; simpl; simpl in IHa2; rewrite IHa2; simpl; omega.
          }
      }
      { simpl in IHa1. simpl in IHa2. destruct n eqn: H.
        - 

      }



 induction (aeval st (APlus a1 a2)) eqn: H. 
    + remember (optimize_0plus_aexp a1) as A1. remember (optimize_0plus_aexp a2) as A2. 
      destruct (optimize_0plus_aexp (APlus a1 a2)) eqn: H0.
      * simpl. destruct n. reflexivity. inversion H. inversion H0. rewrite <- HeqA1 in H3. rewrite <- HeqA2 in H3.
        { destruct a1.
          - destruct n0. simpl in H2. rewrite H3 in IHa2. rewrite H2 in IHa2. inversion IHa2.
            simpl in H2. inversion H2.
          - simpl in H. destruct (st i). destruct (aeval st a2). inversion H0.

        }





remember (optimize_0plus_aexp a1) as A1. remember (optimize_0plus_aexp a2) as A2.
    destruct a1. 
    + destruct n. simpl. rewrite <- HeqA2. apply IHa2. 
      { destruct (aeval st a2) eqn: H.
        - simpl optimize_0plus_aexp. rewrite <- HeqA2. simpl. rewrite H. destruct a2 ; try (simpl; rewrite <- IHa2; omega).
          + destruct n0 ; simpl ; omega.
        - simpl optimize_0plus_aexp. rewrite <- HeqA2. simpl. rewrite H. destruct a2 ; try (simpl; rewrite <- IHa2; omega).
          + destruct n1. inversion H. simpl. omega. 
      } 
    + simpl. rewrite <- HeqA2. rewrite IHa2.
      { destruct (aeval st a2) eqn: H.
        - rewrite <- IHa2. destruct a2 ; try (simpl; rewrite <- IHa2; omega).
          + destruct n ; simpl ; omega.
        - rewrite <- IHa2. destruct a2 ; try (simpl; rewrite <- IHa2; omega).
          + destruct n0. inversion H. simpl. omega.
      }
    + { destruct (aeval st a2) eqn: H.
        - destruct a2.
          + destruct n. simpl. 

destruct (aeval st (APlus a1_1 a1_2)) eqn: H.
        - destruct (aeval st a2) eqn: H0.
          + destruct a2. 
            * destruct n. simpl. 


inversion H. apply plus_is_O in H1. destruct a2.
      
      }
    
*)

  exact FILL_IN_HERE.
Qed.

(*-- Check --*)
Check optimize_0plus_aexp_sound:
  atrans_sound optimize_0plus_aexp.




Fixpoint optimize_0plus_aexp (e:aexp) : aexp := 
  match e with
  | ANum n => 
      ANum n
  | AId i => AId i
  | APlus (ANum 0) e' | APlus e' (ANum 0) =>
      optimize_0plus_aexp e'
  | APlus e1 e2 => 
      APlus (optimize_0plus_aexp e1) (optimize_0plus_aexp e2)
  | AMinus e1 e2 => 
      AMinus (optimize_0plus_aexp e1) (optimize_0plus_aexp e2)
  | AMult e1 e2 => 
      AMult (optimize_0plus_aexp e1) (optimize_0plus_aexp e2)
  end.
