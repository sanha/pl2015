Require Export Assignment10_06.

(* problem #07: 10 points *)


(** **** Exercise: 2 stars (multistep_congr_2)  *)
Lemma multistep_congr_2 : forall t1 t2 t2',
     value t1 ->
     t2 ==>* t2' ->
     P t1 t2 ==>* P t1 t2'.
Proof.
  intros. induction H0.
  - apply multi_refl.
  - assert (P t1 x ==> P t1 y). constructor ; assumption.
    apply multi_R with tm step (P t1 x) (P t1 y) in H2.
    apply multi_trans with (y := P t1 y) ; assumption.
Qed.

(*-- Check --*)
Check multistep_congr_2 : forall t1 t2 t2',
     value t1 ->
     t2 ==>* t2' ->
     P t1 t2 ==>* P t1 t2'.

