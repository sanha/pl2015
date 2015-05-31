Require Export Assignment10_14.

(* problem #15: 10 points *)

(* Hint: 

   First study the chapter "Auto.v".

   Using [;], [try] and [eauto], you can prove it in 7 lines thanks to:. 
     Hint Constructors bstep.

   You can use the following intro pattern:
     destruct ... as [[? | ?] | [? ?]].
*)
Hint Constructors aval.
Hint Constructors astep.
Hint Constructors bstep.

Theorem bexp_strong_progress: forall st b,
  (b = BTrue \/ b = BFalse) \/
  exists b', b / st ==>b b'.
Proof.
  induction b ; intros.
  - left. eauto.
  - left. eauto.
  - right. destruct a. 
    + destruct a0 ;  eauto.
      * assert ((exists n, APlus a0_1 a0_2 = ANum n) \/ (exists a', APlus a0_1 a0_2 / st ==>a a')).
        apply aexp_strong_progress. inversion H. inversion H0. inversion H1. inversion H0. 
        eexists. apply BS_Eq2. eauto. eauto.
      * assert ((exists n, AMinus a0_1 a0_2 = ANum n) \/ (exists a', AMinus a0_1 a0_2 / st ==>a a')).
        apply aexp_strong_progress. inversion H. inversion H0. inversion H1. inversion H0. 
        eexists. apply BS_Eq2. eauto. eauto.
      * assert ((exists n, AMult a0_1 a0_2 = ANum n) \/ (exists a', AMult a0_1 a0_2 / st ==>a a')).
        apply aexp_strong_progress. inversion H. inversion H0. inversion H1. inversion H0. 
        eexists. apply BS_Eq2. eauto. eauto.
    + assert ((exists n, AId i = ANum n) \/ (exists a', AId i  / st ==>a a')). apply aexp_strong_progress.
      eexists. eauto. 
    + assert ((exists n, APlus a1 a2 = ANum n) \/ (exists a', APlus a1 a2  / st ==>a a')). apply aexp_strong_progress.
      inversion H. inversion H0. inversion H1. inversion H0. eexists. eauto.
    + assert ((exists n, AMinus a1 a2 = ANum n) \/ (exists a', AMinus a1 a2  / st ==>a a')). apply aexp_strong_progress.
      inversion H. inversion H0. inversion H1. inversion H0. eexists. eauto.
    + assert ((exists n, AMult a1 a2 = ANum n) \/ (exists a', AMult a1 a2  / st ==>a a')). apply aexp_strong_progress.
      inversion H. inversion H0. inversion H1. inversion H0. eexists. eauto.
  - right. destruct a. 
    + destruct a0 ;  eauto.
      * assert ((exists n, APlus a0_1 a0_2 = ANum n) \/ (exists a', APlus a0_1 a0_2 / st ==>a a')).
        apply aexp_strong_progress. inversion H. inversion H0. inversion H1. inversion H0. 
        eexists. apply BS_LtEq2. eauto. eauto.
      * assert ((exists n, AMinus a0_1 a0_2 = ANum n) \/ (exists a', AMinus a0_1 a0_2 / st ==>a a')).
        apply aexp_strong_progress. inversion H. inversion H0. inversion H1. inversion H0. 
        eexists. apply BS_LtEq2. eauto. eauto.
      * assert ((exists n, AMult a0_1 a0_2 = ANum n) \/ (exists a', AMult a0_1 a0_2 / st ==>a a')).
        apply aexp_strong_progress. inversion H. inversion H0. inversion H1. inversion H0. 
        eexists. apply BS_LtEq2. eauto. eauto.
    + assert ((exists n, AId i = ANum n) \/ (exists a', AId i  / st ==>a a')). apply aexp_strong_progress.
      eexists. eauto. 
    + assert ((exists n, APlus a1 a2 = ANum n) \/ (exists a', APlus a1 a2  / st ==>a a')). apply aexp_strong_progress.
      inversion H. inversion H0. inversion H1. inversion H0. eexists. eauto.
    + assert ((exists n, AMinus a1 a2 = ANum n) \/ (exists a', AMinus a1 a2  / st ==>a a')). apply aexp_strong_progress.
      inversion H. inversion H0. inversion H1. inversion H0. eexists. eauto.
    + assert ((exists n, AMult a1 a2 = ANum n) \/ (exists a', AMult a1 a2  / st ==>a a')). apply aexp_strong_progress.
      inversion H. inversion H0. inversion H1. inversion H0. eexists. eauto.
  - right. destruct b.
    + eexists; constructor.
    + eexists; constructor.
    + inversion IHb. inversion H. inversion H0. inversion H0. inversion H. eexists. eauto. 
    + inversion IHb. inversion H. inversion H0. inversion H0. inversion H. eexists. eauto. 
    + inversion IHb. inversion H. inversion H0. inversion H0. inversion H. eexists. eauto. 
    + inversion IHb. inversion H. inversion H0. inversion H0. inversion H. eexists. eauto. 
  - right. destruct b1. 
    + destruct b2; eauto; try (inversion IHb2; inversion H; inversion H0; inversion H0; inversion H; 
        eexists; eauto).
    + destruct b2; eauto.
    + inversion IHb1. inversion H. inversion H0. inversion H0. inversion H. 
      eexists. eauto. 
    + inversion IHb1. inversion H. inversion H0. inversion H0. inversion H. 
      eexists. eauto.
    + inversion IHb1. inversion H. inversion H0. inversion H0. inversion H. 
      eexists. eauto.
    + inversion IHb1. inversion H. inversion H0. inversion H0. inversion H. 
      eexists. eauto.
Qed.

(*-- Check --*)
Check bexp_strong_progress: forall st b,
  (b = BTrue \/ b = BFalse) \/
  exists b', b / st ==>b b'.

  