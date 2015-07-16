Require Export Assignment11_09.

(* problem #10: 30 points *)

(** Write a type checking function [tyeq: tm -> ty -> bool].
**)

Fixpoint tycheck (t: tm) (T: ty) : bool :=
  match t with
  | ttrue => 
    match T with 
    | TNat => false
    | TBool => true
    end
  | tfalse =>
    match T with 
    | TNat => false
    | TBool => true
    end
  | tif t1 t2 t3 =>
      match (tycheck t1 TBool) with
      | true => 
        match (tycheck t2 T) && (tycheck t3 T) with
        | true => true
        | false => false
        end
      | false => false
      end
  | tzero =>
    match T with
    | TNat => true
    | TBool => false
    end
  | tsucc t1 =>
    match (tycheck t1 TNat) with
    | true => 
      match T with
      | TNat => true
      | TBool => false
      end
    | false => false
    end
  | tpred t1 =>
    match (tycheck t1 TNat) with
    | true => 
      match T with
      | TNat => true
      | TBool => false
      end
    | false => false
    end
  | tiszero t1 =>
    match (tycheck t1 TNat) with
    | true => 
      match T with
      | TNat => false
      | TBool => true
      end
    | false => false
    end
end.

Example tycheck_ex1:
  tycheck
    (tif (tiszero (tpred (tsucc (tsucc tzero)))) ttrue (tiszero (tsucc tzero))) 
    TBool 
  = true.
Proof. compute. reflexivity. Qed.

Example tycheck_ex2:
  tycheck
    (tif (tiszero (tpred (tsucc (tsucc tzero)))) tzero (tiszero (tsucc tzero))) 
    TBool 
  = false.
Proof. compute. reflexivity. Qed.

(** Prove that the type checking function [tyeq: tm -> ty -> bool] is correct.

    Hint: use the lemma [andb_prop].
**)

Check andb_prop.

Theorem tycheck_correct1: forall t T
    (TYCHK: tycheck t T = true),
  |- t \in T.
Proof.
  induction t.
  - destruct T.
    + intros. eauto.
    + intros. inversion TYCHK.
  - destruct T.
    + intros. eauto.
    + intros. inversion TYCHK.
  - destruct T.
    + intros. constructor. 
      * inversion TYCHK. apply IHt1. destruct (tycheck t1 TBool) eqn: H.
        reflexivity. inversion H0.
      * inversion TYCHK. destruct (tycheck t1 TBool) eqn: H.
        { destruct (tycheck t2 TBool && tycheck t3 TBool) eqn: H1.
          apply andb_prop in H1. inversion H1. apply IHt2. assumption.
          inversion H0.
        } inversion H0.
      * inversion TYCHK. destruct (tycheck t1 TBool) eqn: H.
        { destruct (tycheck t2 TBool && tycheck t3 TBool) eqn: H1.
          apply andb_prop in H1. inversion H1. apply IHt3. assumption.
          inversion H0.
        } inversion H0.
    + intros. constructor.
      * inversion TYCHK. apply IHt1. destruct (tycheck t1 TBool) eqn: H.
        reflexivity. inversion H0.
      * inversion TYCHK. destruct (tycheck t1 TBool) eqn: H.
        { destruct (tycheck t2 TNat && tycheck t3 TNat) eqn: H1.
          apply andb_prop in H1. inversion H1. apply IHt2. assumption.
          inversion H0.
        } inversion H0.
      * inversion TYCHK. destruct (tycheck t1 TBool) eqn: H.
        { destruct (tycheck t2 TNat && tycheck t3 TNat) eqn: H1.
          apply andb_prop in H1. inversion H1. apply IHt3. assumption.
          inversion H0.
        } inversion H0.
  - destruct T.
    + intros. inversion TYCHK.
    + intros. eauto.
  - destruct T.
    + intros. inversion TYCHK. destruct (tycheck t TNat) eqn: H; inversion H0.
    + intros. inversion TYCHK ; subst.  destruct (tycheck t TNat) eqn: H.
      * apply IHt in H. eauto.
      * inversion H0.
  - destruct T.
    + intros. inversion TYCHK. destruct (tycheck t TNat) eqn: H; inversion H0.
    + intros. inversion TYCHK ; subst.  destruct (tycheck t TNat) eqn: H.
      * apply IHt in H. eauto.
      * inversion H0.
  - destruct T.
    + intros. inversion TYCHK ; subst. destruct (tycheck t TNat) eqn: H.
      * apply IHt in H. constructor. eauto.
      * inversion H0.
    + intros. inversion TYCHK ; subst. destruct (tycheck t TNat) eqn: H ; inversion H0.
Qed.

Theorem tycheck_correct2: forall t T
    (HASTY: |- t \in T),
  tycheck t T = true.
Proof.
  induction t.
  - destruct T.
    + intros. eauto.
    + intros. inversion HASTY.
  - destruct T.
    + intros. eauto.
    + intros. inversion HASTY.
  - destruct T.
    + intros. inversion HASTY ; subst. apply IHt1 in H2. apply IHt2 in H4.
      apply IHt3 in H5. simpl. rewrite H2. rewrite H4. rewrite H5. reflexivity.
    + intros. inversion HASTY ; subst. apply IHt1 in H2. apply IHt2 in H4.
      apply IHt3 in H5. simpl. rewrite H2. rewrite H4. rewrite H5. reflexivity. 
  - destruct T.
    + intros. inversion HASTY.
    + intros. eauto.
  - destruct T.
    + intros. inversion HASTY.
    + intros. inversion HASTY ; subst. simpl. apply IHt in H0. rewrite H0. reflexivity.
  - destruct T.
    + intros. inversion HASTY.
    + intros. inversion HASTY ; subst. simpl. apply IHt in H0. rewrite H0. reflexivity.
  - destruct T.
    + intros. inversion HASTY ; subst. apply IHt in H0. simpl. rewrite H0. reflexivity.
    + intros. inversion HASTY.
Qed.

(*-- Check --*)

Check (conj tycheck_ex1 tycheck_ex2 :
 (tycheck
    (tif (tiszero (tpred (tsucc (tsucc tzero)))) ttrue (tiszero (tsucc tzero))) 
    TBool 
  = true)
 /\
 (tycheck
    (tif (tiszero (tpred (tsucc (tsucc tzero)))) tzero (tiszero (tsucc tzero))) 
    TBool 
  = false)).

Check tycheck_correct1: forall t T
    (TYCHK: tycheck t T = true),
  |- t \in T.

Check tycheck_correct2: forall t T
    (HASTY: |- t \in T),
  tycheck t T = true.
