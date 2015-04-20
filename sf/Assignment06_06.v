Require Export Assignment06_05.

(* problem #06: 20 points *)

(** **** Exercise: 4 stars, advanced (no_repeats)  *)
(** The following inductively defined proposition... *)

Inductive appears_in {X:Type} (a:X) : list X -> Prop :=
  | ai_here : forall l, appears_in a (a::l)
  | ai_later : forall b l, appears_in a l -> appears_in a (b::l).

(** ...gives us a precise way of saying that a value [a] appears at
    least once as a member of a list [l]. 

    Here's a pair of warm-ups about [appears_in].
*)

Lemma appears_in_app : forall (X:Type) (xs ys : list X) (x:X), 
     appears_in x (xs ++ ys) -> appears_in x xs \/ appears_in x ys.
Proof.
  intros X. induction xs as [| xs'].
  - intros. simpl in H. induction ys as [| ys'].
    + left. apply H.
    + right. apply H.
  - intros. inversion H.
    + left. apply ai_here.
    + inversion H1.
      * apply IHxs in H1. inversion H1. left. apply ai_later. apply H3. right. apply H3.
      * apply IHxs in H1. inversion H1. left. apply ai_later. apply H5. right. apply H5.
Qed.


Lemma l_apps_nil: forall {X: Type} (l: list X), l++[] = l.
Proof.
  intros. induction l as [| l']. simpl. reflexivity. simpl. rewrite -> IHl. reflexivity.
Qed.


Lemma app_appears_in : forall (X:Type) (xs ys : list X) (x:X), 
     appears_in x xs \/ appears_in x ys -> appears_in x (xs ++ ys).
Proof.
  intros X. induction xs as [| xs'].
  - intros. induction ys as [| ys'].
    + simpl. inversion H. apply H0. apply H0.
    + simpl. simpl in IHys. inversion H. inversion H0. apply H0.
  - intros. inversion H.
    + inversion H0.
      * simpl. apply ai_here.
      * simpl. apply or_introl with (Q:= appears_in x ys) in H2. apply IHxs in H2. apply ai_later. apply H2.
    + simpl. apply ai_later. apply IHxs. right. apply H0.
Qed.
