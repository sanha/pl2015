Require Export Assignment08_02.

(* problem #03: 10 points *)

(** **** Exercise: 3 stars (loop_never_stops)  *)
Theorem loop_never_stops : forall st st',
  ~(loop / st || st').
Proof.
  intros st st' cont. unfold loop in cont.
  remember (WHILE BTrue DO SKIP END) as loopdef eqn:Heqloopdef.
    (* Proceed by induction on the assumed derivation showing that
     [loopdef] terminates.  Most of the cases are immediately
     contradictory (and so can be solved in one step with
     [inversion]). *)
  induction cont ; try inversion Heqloopdef.
  - subst. inversion H.
  - subst. apply IHcont2. assumption.
Qed.

(*-- Check --*)
Check loop_never_stops : forall st st',
  ~(loop / st || st').

