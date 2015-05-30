Require Export Assignment10_07.

(* problem #08: 10 points *)

(** **** Exercise: 3 stars (eval__multistep)  *)
(** The key idea behind the proof comes from the following picture:
       P t1 t2 ==>            (by ST_Plus1) 
       P t1' t2 ==>           (by ST_Plus1)  
       P t1'' t2 ==>          (by ST_Plus1) 
       ...                
       P (C n1) t2 ==>        (by ST_Plus2)
       P (C n1) t2' ==>       (by ST_Plus2)
       P (C n1) t2'' ==>      (by ST_Plus2)
       ...                
       P (C n1) (C n2) ==>    (by ST_PlusConstConst)
       C (n1 + n2)              
    That is, the multistep reduction of a term of the form [P t1 t2]
    proceeds in three phases:
       - First, we use [ST_Plus1] some number of times to reduce [t1]
         to a normal form, which must (by [nf_same_as_value]) be a
         term of the form [C n1] for some [n1].
       - Next, we use [ST_Plus2] some number of times to reduce [t2]
         to a normal form, which must again be a term of the form [C
         n2] for some [n2].
       - Finally, we use [ST_PlusConstConst] one time to reduce [P (C
         n1) (C n2)] to [C (n1 + n2)]. *)

(** To formalize this intuition, you'll need to use the congruence
    lemmas from above (you might want to review them now, so that
    you'll be able to recognize when they are useful), plus some basic
    properties of [==>*]: that it is reflexive, transitive, and
    includes [==>]. *)

(** **** Exercise: 2 stars (multistep_congr_2)  *)
Lemma multistep_congr_1 : forall t1 t1' t2,
     t1 ==>* t1' ->
     P t1 t2 ==>* P t1' t2.
Proof.
  intros t1 t1' t2 H. multi_cases (induction H) Case.
    Case "multi_refl". apply multi_refl. 
    Case "multi_step". apply multi_step with (P y t2). 
        apply ST_Plus1. apply H. 
        apply IHmulti.  Qed.

Lemma nf_is_value : forall t,
  normal_form step t -> value t.
Proof. (* a corollary of [strong_progress]... *)
  unfold normal_form. intros t H.
  assert (G : value t \/ exists t', t ==> t').
    SCase "Proof of assertion". apply strong_progress.
  inversion G.
    SCase "l". apply H0.
    SCase "r". apply ex_falso_quodlibet. apply H. assumption.  Qed.

Theorem eval__multistep : forall t n,
  t || n -> t ==>* C n.
Proof.
  intros. induction H.
  - apply multi_refl.
  - assert (P t1 t2 ==>* P (C n1) t2).
    apply multistep_congr_1. assumption.
    assert (P (C n1) t2 ==>* P (C n1) (C n2)).
    apply multistep_congr_2 ; try assumption. apply nf_is_value. unfold normal_form.
    intros contra. inversion contra. inversion H2.
    assert (P (C n1) (C n2) ==> C (n1 + n2)).
    constructor. apply multi_trans with (y := P (C n1) t2) ; try assumption.
    apply multi_trans with (y := P (C n1) (C n2)) ; try assumption.
    apply multi_R with tm step (P (C n1) (C n2)) (C (n1 + n2)) in H3. assumption.
Qed.

(*-- Check --*)
Check eval__multistep : forall t n,
  t || n -> t ==>* C n.

