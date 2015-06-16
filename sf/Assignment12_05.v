Require Export Assignment12_04.

(* problem #05: 20 points *)

(** Translate this informal recursive definition into one using [fix]:
<<
   halve = 
     \x:Nat. 
        if x=0 then 0 
        else if (pred x)=0 then 0
        else 1 + (halve (pred (pred x))))
>>
*)

Definition halve : tm :=
tfix (tabs Halve (TArrow TNat TNat)
       (tabs X TNat
         (tif0 (tvar X) (tnat 0)
           (tif0 (tpred (tvar X)) (tnat 0)
             (tsucc (tapp (tvar Halve) (tpred (tpred (tvar X))))))))).

Hint Unfold halve.

Example halve_type: empty |- halve \in TArrow TNat TNat.
Proof. unfold halve ; eauto 10. Qed.

Example halve_10: tapp halve (tnat 10) ==>* tnat 5.
Proof. unfold halve ; normalize. Qed.

Example halve_11: tapp halve (tnat 11) ==>* tnat 5.
Proof. unfold halve; normalize. Qed.


Lemma halve_supp: forall t t', t ==>* t' -> (tsucc t) ==>* (tsucc t').
Proof.
  intros. induction H. constructor. assert (tsucc x ==> tsucc y).
  constructor. assumption. apply multi_step with (tsucc y); assumption.
Qed.

Theorem halve_correct: forall n,
   tapp halve (tnat (n+n)) ==>* tnat n.
Proof.
  intros. induction n.
  - simpl. unfold halve. normalize.
  - assert (tapp halve (tnat (S n + S n)) ==>* tsucc (tapp halve (tnat (n + n)))).
    + assert (S n + S n = S (S (n + n))). omega. rewrite H.  
      unfold halve. eapply multi_step. apply ST_AppFix. eauto. eauto.
      eapply multi_step. apply ST_App1. eauto. 
      repeat (eapply multi_step; compute; eauto).
    + apply multi_trans with (y:= tsucc (tapp halve (tnat (n + n)))).
      assumption. assert (tsucc (tapp halve (tnat (n + n))) ==>* tsucc (tnat n)).
      apply halve_supp. assumption. apply multi_trans with (y:= tsucc (tnat n)).
      assumption. apply multi_step with (tnat (S n)). constructor. eauto.
Qed.



(*-- Check --*)

Check conj halve_type (conj halve_10 halve_11) :
  empty |- halve \in TArrow TNat TNat /\
  tapp halve (tnat 10) ==>* tnat 5 /\ 
  tapp halve (tnat 11) ==>* tnat 5.

Check halve_correct: forall n,
   tapp halve (tnat (n + n)) ==>* tnat n.

