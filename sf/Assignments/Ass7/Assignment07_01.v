Require Export Assignment07_00.

(* problem #01: 20 points *)


(** **** Exercise: 3 stars (optimize_0plus_b)  *)
(** Since the [optimize_0plus] tranformation doesn't change the value
    of [aexp]s, we should be able to apply it to all the [aexp]s that
    appear in a [bexp] without changing the [bexp]'s value.  Write a
    function which performs that transformation on [bexp]s, and prove
    it is sound.  Use the tacticals we've just seen to make the proof
    as elegant as possible. *)

Fixpoint optimize_0plus_b (b : bexp) : bexp :=
  match b with
  | BEq a1 a2 => BEq (optimize_0plus a1) (optimize_0plus a2)
  | BLe a1 a2 => BLe (optimize_0plus a1) (optimize_0plus a2)
  | _ => b
  end.

Theorem optimize_0plus_sound: forall a,
  aeval (optimize_0plus a) = aeval a.
Proof.
  intros a. induction a ; simpl ;auto.
  - destruct a1 ; simpl ; auto.
    + destruct n. 
      * auto. 
      * simpl. auto.
Qed.

Theorem optimize_0plus_b_sound : forall b,
  beval (optimize_0plus_b b) = beval b.
Proof.
  intros. destruct b ; try simpl ; repeat try rewrite optimize_0plus_sound; try auto.
Qed.
(** [] *)