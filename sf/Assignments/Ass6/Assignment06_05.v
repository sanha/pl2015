Require Export Assignment06_04.

(* problem #05: 20 points *)

(** **** Exercise: 3 stars (all_forallb)  *)
(** Inductively define a property [all] of lists, parameterized by a
    type [X] and a property [P : X -> Prop], such that [all X P l]
    asserts that [P] is true for every element of the list [l]. *)

Inductive all {X : Type} (P : X -> Prop) : list X -> Prop :=
  | all_base : all P nil
  | all_tail : forall (l : list X) (x : X), P x -> all P l -> all P (x::l)
.

(** Recall the function [forallb], from the exercise
    [forall_exists_challenge] in chapter [Poly]: *)

Fixpoint forallb {X : Type} (test : X -> bool) (l : list X) : bool :=
  match l with
    | [] => true
    | x :: l' => andb (test x) (forallb test l')
  end.

(** Using the property [all], write down a specification for [forallb],
    and prove that it satisfies the specification. Try to make your 
    specification as precise as possible.

    Are there any important properties of the function [forallb] which
    are not captured by your specification? *)

Lemma forallb_tail: forall {X: Type} (P: X -> bool) (l': X) (l: list X), forallb P (l' :: l) = true -> forallb P l = true.
Proof.
  intros. inversion H. destruct (P l').
  - destruct (forallb P l). simpl. reflexivity. simpl. reflexivity.
  - destruct (forallb P l). simpl in H1. inversion H1. simpl. reflexivity. 
Qed.
Lemma forallb_head: forall {X: Type} (P: X -> bool) (l': X) (l: list X), forallb P (l' :: l) = true -> P l' = true.
Proof.
  intros. inversion H. destruct (P l').
  - destruct (forallb P l). simpl. reflexivity. inversion H1.
  - destruct (forallb P l). simpl. reflexivity. inversion H1.
Qed.

Theorem forallb_correct: forall X (P: X -> bool) l,
  forallb P l = true <-> all (fun x => P x = true) l.
Proof.
  intros. split.
  - intros. induction l as [| l'].
    + apply all_base.
    + apply all_tail.
      * apply forallb_head with P l' l in H. apply H.
      * apply IHl. apply forallb_tail with P l' l in H. apply H.
  - intros. induction l as [| l'].
    + simpl. reflexivity.
    + inversion H. simpl. rewrite -> H2. apply IHl in H3. rewrite -> H3. simpl. reflexivity.
Qed.

(** [] *)

