Require Export Assignment12_02.

(* problem #03: 10 points *)

(** **** Exercise: 3 stars (types_unique)  *)
(** Another pleasant property of the STLC is that types are
    unique: a given term (in a given context) has at most one
    type. *)

Lemma type_is_unique: forall t G T T'
    (TYPED: G |- t \in T)
    (TYPED': G |- t \in T'),
  T = T'.
Proof.
  intros t. induction t; subst ; intros ; (inversion TYPED ; subst) ; (inversion TYPED' ; subst); try auto.
  - rewrite H2 in H1. inversion H1. reflexivity.
  - apply IHt1 with G (TArrow T1 T) (TArrow T0 T') in H2. inversion H2. reflexivity. assumption.
  - apply IHt with (extend G i t) T12 T0 in H4. rewrite H4. auto. assumption.
  - apply IHt2 with G T T' in H5 ; assumption.
  - apply IHt1 with G T1 T0 in H2. rewrite H2. apply IHt2 with G T2 T3 in H4. rewrite H4.
    eauto. eauto. eauto.
  - apply IHt with G (TProd T T2) (TProd T' T0) in H1. inversion H1. reflexivity. assumption.
  - apply IHt with G (TProd T1 T) (TProd T0 T') in H1. inversion H1. reflexivity. assumption.
  - apply IHt1 with G T1 T0 in H4. rewrite H4 in H5. apply IHt2 with (extend G i T0) T T' in H5 ; assumption.
    assumption. 
  - apply IHt with G T1 T0 in H3. rewrite H3. auto. auto.
  - apply IHt with G T2 T0 in H3. rewrite H3. auto. auto.
  - apply IHt1 with G (TSum T1 T2) (TSum T0 T3) in H6. inversion H6 ; subst.
    apply IHt2 with (extend G i T0) T' T in H10. auto. auto. auto.
  - apply IHt1 with G T1 T0 in H2. rewrite H2. auto. auto.
  - apply IHt2 with G T T' in H7. auto. auto.
  - apply IHt with G (TArrow (TArrow T1 T2) (TArrow T1 T2)) (TArrow (TArrow T0 T3) (TArrow T0 T3)) in H1.
    inversion H1 ; subst. auto. auto.
Qed.

(*-- Check --*)
Check type_is_unique: forall t G T T'
    (HTyped: G |- t \in T)
    (HTyped': G |- t \in T'),
  T = T'.

