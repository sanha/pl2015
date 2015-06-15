Require Export Assignment12_01.

(* problem #02: 10 points *)

(** **** Exercise: 2 stars, optional (typable_empty__closed)  *)
Corollary typable_empty__closed : forall t T, 
    empty |- t \in T  ->
    closed t.
Proof.
  unfold closed. intros. intros contra. induction t ; 
    try (apply free_in_context with (T:= T) (Gamma:= empty) in contra;
    inversion contra; inversion H0; assumption).
Qed.

(*-- Check --*)
Check typable_empty__closed : forall t T, 
    empty |- t \in T  ->
    closed t.

