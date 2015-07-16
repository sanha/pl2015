Require Export Assignment11_01.

(* problem #02: 10 points *)

(** **** Exercise: 3 stars, advanced (value_is_nf)  *)
(** Hint: You will reach a point in this proof where you need to
    use an induction to reason about a term that is known to be a
    numeric value.  This induction can be performed either over the
    term itself or over the evidence that it is a numeric value.  The
    proof goes through in either case, but you will find that one way
    is quite a bit shorter than the other.  For the sake of the
    exercise, try to complete the proof both ways. *)

Lemma value_is_nf : forall t,
  value t -> step_normal_form t.
Proof.
  intros. inversion H. 
  { inversion H0.
    - unfold normal_form. intros contra. inversion contra. solve by inversion.
    - unfold normal_form. intros contra. inversion contra. solve by inversion.
  }
  { induction H0.
    - unfold normal_form. intros contra. inversion contra. solve by inversion.
    - unfold normal_form. intros contra. inversion contra. inversion H1 ; subst.
      assert (value t). unfold value. right. apply H0.
      apply IHnvalue in H2. unfold normal_form in H2. unfold not in H2.
      assert (exists t': tm, t ==> t'). exists t1'. assumption. apply H2 in H4. inversion H4.
  }
Qed.

(*-- Check --*)
Check value_is_nf : forall t,
  value t -> step_normal_form t.

