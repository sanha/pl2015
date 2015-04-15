Require Export Assignment05_27.

(* problem #28: 30 points *)


(** 4 stars (palindromes)  *)
(** A palindrome is a sequence that reads the same backwards as
    forwards.

    - Define an inductive proposition [pal] on [list X] that
      captures what it means to be a palindrome. (Hint: You'll need
      three cases.  Your definition should be based on the structure
      of the list; just having a single constructor
        c : forall l, l = rev l -> pal l
      may seem obvious, but will not work very well.)
 
    - Prove [pal_app_rev] that 
       forall l, pal (l ++ rev l).
    - Prove [pal_rev] that 
       forall l, pal l -> l = rev l.
*)

Inductive pal {X: Type} : list X -> Prop :=
  | pal_0 :  pal nil
  | pal_1:  forall x: X, pal (x :: nil)
  | pal_add: forall (x: X) (l: list X), pal l -> pal (x:: (snoc l x))
.

Lemma app_snoc : forall {X: Type} (l : list X) (x1 x2: X), x1 :: snoc l x2 = snoc (x1 :: l) x2.
Proof.
  intros. induction l as [| l'].
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

Lemma app_list_snoc : forall {X: Type} (l1 l2: list X) (x: X), l1 ++ snoc l2 x = snoc (l1++l2) x.
Proof.
  intros. induction l1 as [| l1'].
  - simpl. reflexivity.
  - simpl. rewrite -> IHl1. reflexivity.
Qed.

Theorem pal_app_rev: forall (X: Type) (l: list X),
  pal (l ++ rev l).
Proof.
  intros. induction l as [| l'].
  - simpl. apply pal_0.
  - simpl. rewrite -> app_list_snoc. apply pal_add. apply IHl.
Qed.


Lemma rev_snoc: forall {X: Type} (l: list X) (x: X), rev (snoc l x) = x :: rev l.
Proof.
  intros. induction l as [| l'].
  - simpl. reflexivity.
  - simpl. rewrite -> IHl. apply app_snoc.
Qed.


Theorem pal_rev: forall (X: Type) (l: list X),
  pal l -> l = rev l.
Proof.
  intros X l H. induction H.
  - simpl. reflexivity.
  - simpl. reflexivity.
  - simpl. rewrite -> rev_snoc. rewrite <- IHpal. apply app_snoc. 
Qed.

(** [] *)




