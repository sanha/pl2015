Require Export Assignment10_15.

(* problem #16: 10 points *)

(* Hint: 

   First study the chapter "Auto.v".

   Using [;], [try] and [eauto], you can prove it in 6 lines thanks to:
     Hint Constructors cstep.
 
   You can use the following intro pattern:
     destruct ... as [ | [? [? ?]]].
*)

Hint Constructors cstep.

Theorem cimp_strong_progress : forall c st,
  c = SKIP \/ 
  exists c' st', c / st ==>c c' / st'.
Proof.
  intros. induction c.
  - left. reflexivity.
  - right. destruct a ; eauto. 
    + assert ((exists n, APlus a1 a2 = ANum n) \/ (exists a', APlus a1 a2 / st ==>a a')).
      apply aexp_strong_progress. inversion H. inversion H0. inversion H1. inversion H0.
      eexists. eauto.
    + assert ((exists n, AMinus a1 a2 = ANum n) \/ (exists a', AMinus a1 a2 / st ==>a a')).
      apply aexp_strong_progress. inversion H. inversion H0. inversion H1. inversion H0.
      eexists. eauto.
    + assert ((exists n, AMult a1 a2 = ANum n) \/ (exists a', AMult a1 a2 / st ==>a a')).
      apply aexp_strong_progress. inversion H. inversion H0. inversion H1. inversion H0.
      eexists. eauto.  
  - right. destruct c1; eauto.
    + inversion IHc1. inversion H. inversion H. inversion H0. eexists. eexists. eauto.
    + inversion IHc1. inversion H. inversion H. inversion H0. eexists. eexists. eauto.
    + inversion IHc1. inversion H. inversion H. inversion H0. eexists. eexists. eauto.
    + inversion IHc1. inversion H. inversion H. inversion H0. eexists. eexists. eauto.
  - right. destruct b ; eauto.
    + assert ((BEq a a0 = BTrue \/ BEq a a0 = BFalse) \/ exists b', BEq a a0 / st ==>b b').
      apply bexp_strong_progress. inversion H. inversion H0. inversion H1. inversion H1. inversion H0.
      eexists. eexists. eauto.
    + assert ((BLe a a0= BTrue \/ BLe a a0 = BFalse) \/ exists b', BLe a a0 / st ==>b b').
      apply bexp_strong_progress. inversion H. inversion H0. inversion H1. inversion H1. inversion H0.
      eexists. eexists. eauto.
    + assert ((BNot b = BTrue \/ BNot b = BFalse) \/ exists b', BNot b / st ==>b b').
      apply bexp_strong_progress. inversion H. inversion H0. inversion H1. inversion H1. inversion H0.
      eexists. eexists. eauto.
    + assert ((BAnd b1 b2 = BTrue \/ BAnd b1 b2 = BFalse) \/ exists b', BAnd b1 b2/ st ==>b b').
      apply bexp_strong_progress. inversion H. inversion H0. inversion H1. inversion H1. inversion H0.
      eexists. eexists. eauto.
  - right. destruct b ; eauto.
  - right. destruct c1 ; eauto.
    + inversion IHc2. rewrite H. eexists. eauto. inversion H. inversion H0.
      eexists. eexists. eauto.
    + inversion IHc1. inversion H. inversion H. inversion H0. eexists.  eauto.
    + inversion IHc1. inversion H. inversion H. inversion H0. eexists.  eauto.
    + inversion IHc1. inversion H. inversion H. inversion H0. eexists.  eauto.
    + inversion IHc1. inversion H. inversion H. inversion H0. eexists.  eauto. 
Qed.

(*-- Check --*)
Check cimp_strong_progress : forall c st,
  c = SKIP \/ 
  exists c' st', c / st ==>c c' / st'.
