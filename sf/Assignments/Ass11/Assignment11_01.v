Require Export Assignment11_00.

(* problem #01: 10 points *)

(** **** Exercise: 2 stars (some_term_is_stuck)  *)
Example some_term_is_stuck :
  exists t, stuck t.
Proof.
  exists (tif tzero ttrue tzero). unfold stuck. split.
  - unfold normal_form. intros contra. inversion contra.
    inversion H ; subst. inversion H4.
  - intros contra. inversion contra; solve by inversion.
Qed.

(*-- Check --*)
Check some_term_is_stuck :
  exists t, stuck t.

