Require Export Assignment12_05.

(* problem #06: 10 points *)

Theorem MoreStlc_value_is_nf: forall v t,
  value v -> v ==> t -> False.
Proof with eauto.
  intros; generalize dependent t; assert (normal_form step v)...
  unfold normal_form; intros; induction H; intros contra; destruct contra;
  try solve by inversion; try inversion H0; try inversion H1; subst...
Qed.

Hint Resolve MoreStlc_value_is_nf.

Theorem MoreStlc_deterministic:
  deterministic step.
Proof with eauto.
  unfold deterministic; intros; generalize dependent y2;
  induction H as [| |? ? ? ? P| | | | | |? ? ? ? P| | | | | |? ? ? ? P| |? ? ? P|
  |? ? ? P| | | | | | | | |? ? ? ? P| | | ? ? ? ? ? ? P| |? ? ? P]; intros;
  inversion H0; subst; try solve by inversion;
  try replace t0'0 with t0';
  try replace t1'0 with t1';
  try replace t2'0 with t2';
  eauto; exfalso...
Qed.

Lemma determ_supp: forall t t1 t2:tm, t ==> t1 -> t ==> t2 -> t1 = t2.
Proof.
  apply MoreStlc_deterministic.
Qed.


Lemma looping: forall t q1 q2 q3, q1 ==>* t -> q1 ==> q2 -> q2 ==> q3 -> q3 ==> q1 -> 
                (t = q1 \/ t = q2 \/ t = q3).
Proof.
  intros t q1 q2 q3 H. generalize dependent q2. generalize dependent q3.
  induction H. intros. left. auto.
  intros. assert (y = q2). apply determ_supp with (t:= x) ; assumption. subst y.
  assert (z = q2 \/ z = q3 \/ z = x). apply IHmulti ; assumption.
  destruct H4. right. left. assumption. destruct H4. right. right. assumption.
  left. assumption.
Qed.

Theorem tloop_diverges:
  ~ exists t, tapp tloop (tnat 0) ==>* t /\ normal_form step t.
Proof.
  intros contra. inversion contra. inversion H. unfold normal_form in H1.
  unfold not in H1. assert (value tloop). unfold tloop. eauto. 
  remember (tabs Loop (TArrow TNat TNat) (tabs X TNat (tapp (tvar Loop) (tvar X)))) as F1.
  assert (value F1). rewrite HeqF1. eauto. remember (tnat 0) as v1. assert (value v1). rewrite Heqv1. eauto.
  unfold tloop in H0. rewrite <- HeqF1 in H0.
  assert (tapp (tfix F1) v1 ==> tapp (tapp F1 (tfix F1)) v1). apply ST_AppFix ; assumption. 
  assert (forall t', tapp (tfix F1) v1 ==> t' -> t' = tapp (tapp F1 (tfix F1)) v1). 
  intros. apply determ_supp with (t:= tapp (tfix F1) v1) ; assumption.
  assert (value (tfix F1)). rewrite HeqF1. eauto.
  remember (tfix F1) as v2. remember (tabs X TNat (tapp (tvar Loop) (tvar X))) as t12.
  assert (tapp (tapp F1 v2) v1 ==> tapp ([Loop := v2]t12) v1). rewrite HeqF1. apply ST_App1.
  apply ST_AppAbs. assumption.
  assert (forall t', tapp (tapp F1 v2) v1 ==> t' -> t' = tapp ([Loop := v2]t12) v1). intros.
  apply determ_supp with (t:= tapp (tapp F1 v2) v1) ; assumption.
  assert (tapp ([Loop := v2]t12) v1 = tapp (tabs X TNat (tapp v2 (tvar X)))v1). 
  rewrite Heqt12. simpl. reflexivity. rewrite H10 in H9.
  assert (value (tabs X TNat (tapp v2 (tvar X)))). eauto.
  assert (tapp (tabs X TNat (tapp v2 (tvar X))) v1 ==> [X := v1](tapp v2 (tvar X))). eauto.
  assert (forall t', tapp (tabs X TNat (tapp v2 (tvar X))) v1 ==> t' -> t' = [X := v1](tapp v2 (tvar X))).
  intros. apply determ_supp with (t:= tapp (tabs X TNat (tapp v2 (tvar X))) v1) ; assumption.
  assert ([X := v1]tapp v2 (tvar X) = tapp tloop v1). rewrite Heqv1. rewrite Heqv2. simpl. rewrite HeqF1.
  rewrite Heqt12. auto. assert (tapp tloop v1 = tapp v2 v1). rewrite Heqv1. rewrite Heqv2. unfold tloop.
  rewrite HeqF1. rewrite Heqt12. reflexivity. rewrite <- H15 in H6. rewrite <-H15 in H5.
  clear H3 H4 H7 H2. remember (tapp tloop v1) as q1. remember (tapp (tapp F1 v2) v1) as q2.
  rewrite H10 in H8. remember (tapp (tabs X TNat (tapp v2 (tvar X))) v1) as q3.
  rewrite H14 in H12. rewrite H14 in H13. clear H10 H14. clear HeqF1 Heqt12 H0. inversion H. clear H2.
  { assert (x = q1 \/ x = q2 \/ x = q3). apply looping; assumption.
    destruct H2. subst x. eauto. 
    destruct H2. subst x. eauto.
    subst x. eauto.
  } 
Qed.

(*-- Check --*)
Check tloop_diverges:
  ~ exists t, tapp tloop (tnat 0) ==>* t /\ normal_form step t.
