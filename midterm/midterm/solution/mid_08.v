Require Export mid_07.

(* problem #08: 30 points *)

(** Easy:
    Define a predicate [sorted_min: nat -> list nat -> Prop], where
    [sorted_min n l] holds iff the elements in the list [l] is greater
    than or equal to [n] and sorted in the increasing order.
 **)

Inductive sorted_min: nat -> list nat -> Prop :=
  | sorted_nil n : sorted_min n []
  | sorted_cons n m l (LE: n <= m) (SORTED: sorted_min m l)
    : sorted_min n (m :: l)
.

Example sorted_min_example1: sorted_min 0 [1; 3; 4; 4; 5].
Proof. repeat (constructor; auto). Qed.


Example sorted_min_example2: sorted_min 2 [2; 2; 3; 6].
Proof. repeat (constructor ; auto). Qed.

Example sorted_min_non_example1: sorted_min 1 [0; 1] -> False.
Proof. intros. inversion H. inversion LE. Qed.




(** Medium:
    Prove the following theorem. 
 **)

Inductive appears_in (n : nat) : list nat -> Prop :=
| ai_here : forall l, appears_in n (n::l)
| ai_later : forall m l, appears_in n l -> appears_in n (m::l).

Lemma sorted_not_in: forall n m l
    (SORTED: sorted_min m l)
    (LT: n < m),
  ~ appears_in n l.
Proof.
  intros n m l; revert m.
  induction l; intros ; intros IN.
  - inversion IN.
  - inversion SORTED; subst.
    inversion IN ; subst.
    + apply le_not_lt in LE; auto.
    + apply IHl with (m:= x); auto.
      apply lt_le_trans with (m:= m); auto.
Qed.









(** Hard:
    Prove the following theorem.
 **)

(* [beq_nat n m] returns [true]  if [n = m] holds; 
                 returns [false] otherwise. *)
Check beq_nat.
Check beq_nat_false.
Check beq_nat_true.
Check beq_nat_refl.

(* [ltb n m] returns [true]  if [n < m] holds; 
             returns [false] otherwise.
   Note that [ltb n m] is displayed as [n <? m]. *)
Check ltb.
Check ltb_lt.

Fixpoint appears_inb (n: nat) (l: list nat) : bool :=
  match l with
  | nil => false
  | m :: l' => 
    if ltb n m
    then false
    else (if beq_nat n m
          then true
          else appears_inb n l')
  end.

Theorem appears_inb_correct: forall n l
    (SORTED: sorted_min 0 l)
    (NOTAPPEAR: appears_inb n l = false),
  ~ appears_in n l.
Proof.
  generalize 0 as m.
  intros; revert m SORTED NOTAPPEAR.
  induction l; intros; intro IN.
  - inversion IN.
  - simpl in NOTAPPEAR.
    inversion SORTED; subst.
    destruct (n<?x) eqn: NA.
    + apply ltb_lt in NA.
      inversion IN; subst.
      * apply lt_irrefl in NA; auto.
      * apply sorted_not_in with (n:=n) in SORTED0; auto.
    + destruct (beq_nat n x) eqn: EQ.
      * inversion NOTAPPEAR.
      * apply beq_nat_false in EQ.
        inversion IN; subst; auto.
        apply IHl with (m:=x); auto.
Qed.

