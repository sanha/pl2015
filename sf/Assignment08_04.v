Require Export Assignment08_03.

(* problem #04: 10 points *)

(** **** Exercise: 4 stars (no_whiles_terminating)  *)
(** Imp programs that don't involve while loops always terminate.
    State and prove a theorem [no_whiles_terminating] that says this. *)

(* Hint *)
Check andb_true_iff.

Theorem no_whiles_terminate: forall c st
    (NOWHL: no_whiles c = true),
  exists st', c / st || st'.
Proof.
  intros c st. intros NW. generalize dependent st. induction c ; intros.
  - exists st. apply E_Skip.
  - remember (aeval st a) as n eqn:Hn. exists (update st i n). apply E_Ass. symmetry. assumption.
  - inversion NW. apply andb_true_iff in H0. inversion H0. apply IHc1 with (st := st) in H.
    inversion H as [ev1]. apply IHc2 with (st := ev1) in H1. inversion H1 as [ev2]. exists ev2.
    apply E_Seq with (st' := ev1) ; assumption.
  - inversion NW. apply andb_true_iff in H0. inversion H0. apply IHc1 with (st := st) in H.
    apply IHc2 with (st := st) in H1. inversion H as [ev1]. inversion H1 as [ev2]. remember (beval st b) as b0 eqn: B.
    symmetry in B. destruct b0. 
    + exists ev1. apply E_IfTrue ; assumption.
    + exists ev2. apply E_IfFalse ; assumption.
  - inversion NW.
Qed.

(*-- Check --*)
Check no_whiles_terminate: forall c st
    (NOWHL: no_whiles c = true),
  exists st', c / st || st'.

