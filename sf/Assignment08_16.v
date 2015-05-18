Require Export Assignment08_15.

(* problem #16: 10 points *)

Lemma optimize_0plus_aexp_sound:
  atrans_sound optimize_0plus_aexp.
Proof.
  unfold atrans_sound. unfold aequiv. intros. induction a ; try reflexivity.
  - remember (optimize_0plus_aexp a1) as A1. remember (optimize_0plus_aexp a2) as A2.
    destruct a1. 
    + destruct n. simpl. rewrite <- HeqA2. apply IHa2.
      simpl.

      destruct a2. destruct n0. simpl. omega. simpl. omega. simpl. omega.
      simpl optimize_0plus_aexp.

 simpl. destruct (optimize_0plus_aexp a1) ; try (rewrite IHa1; rewrite IHa2 ; reflexivity).
    + destruct n. rewrite IHa1. simpl. rewrite IHa2.
 rewrite IHa1. rewrite IHa2. 


 induction (APlus a1 a2) ; try reflexivity.
    + simpl.

simpl optimize_0plus_aexp. induction a1. induction n. simpl. apply IHa2.
    destruct a2. induction n0 ; try (simpl ; omega). simpl. omega.
    simpl. omega.

 destruct a1.
    + induction n.
      * simpl. apply IHa2.
      * destruct a2. simpl. 


 destruct a1. destruct a2.
    + induction n ; try reflexivity. induction n0 ; try reflexivity. simpl. rewrite plus_0_r. reflexivity.
    + induction n.

 simpl.


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
