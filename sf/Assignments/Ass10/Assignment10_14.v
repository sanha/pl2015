Require Export Assignment10_13.

(* problem #14: 10 points *)

(* Hint: 

   First study the chapter "Auto.v".

   Using [;], [try] and [eauto], you can prove it in 4 lines thanks to: 
     Hint Constructors aval
     Hint Constructors astep.
  
   You can use the following intro pattern:
     destruct ... as [[? ?] | [? ?]].
*)

Hint Constructors aval.
Hint Constructors astep.

Theorem aexp_strong_progress: forall st a,
  (exists n, a = ANum n) \/
  exists a', a / st ==>a a'.
Proof.
  intros. induction a ; intros.
  - left. eauto.
  - right. eauto.
  - right. destruct a1.
    + destruct a2 ; eauto ; try (inversion IHa2; inversion H; inversion H0;
        inversion H; eexists; apply AS_Plus2; eauto; eauto).
    + inversion IHa1. inversion H. inversion H0. inversion H. eexists. 
      apply AS_Plus1. eauto.
    + inversion IHa1. inversion H. inversion H0. inversion H. eexists. 
      apply AS_Plus1. eauto.
    + inversion IHa1. inversion H. inversion H0. inversion H. eexists. 
      apply AS_Plus1. eauto.
    + inversion IHa1. inversion H. inversion H0. inversion H. eexists. 
      apply AS_Plus1. eauto.
  - right. destruct a1.
    + destruct a2 ; eauto ; try (inversion IHa2; inversion H; inversion H0;
        inversion H; eexists; apply AS_Minus2; eauto; eauto).
    + inversion IHa1. inversion H. inversion H0. inversion H. eexists. 
      constructor. eauto.
    + inversion IHa1. inversion H. inversion H0. inversion H. eexists. 
      constructor. eauto.
    + inversion IHa1. inversion H. inversion H0. inversion H. eexists. 
      constructor. eauto.
    + inversion IHa1. inversion H. inversion H0. inversion H. eexists. 
      constructor. eauto.
  - right. destruct a1.
    + destruct a2 ; eauto ; try (inversion IHa2; inversion H; inversion H0;
        inversion H; eexists; apply AS_Mult2; eauto; eauto).
    + inversion IHa1. inversion H. inversion H0. inversion H. eexists. 
      constructor. eauto.
    + inversion IHa1. inversion H. inversion H0. inversion H. eexists. 
      constructor. eauto.
    + inversion IHa1. inversion H. inversion H0. inversion H. eexists. 
      constructor. eauto.
    + inversion IHa1. inversion H. inversion H0. inversion H. eexists. 
      constructor. eauto.
Qed.

(*-- Check --*)
Check aexp_strong_progress: forall st a,
  (exists n, a = ANum n) \/
  exists a', a / st ==>a a'.

