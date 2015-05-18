Require Export Assignment06_07.

(* problem #08: 40 points *)

(** **** Exercise: 4 stars, advanced (pigeonhole principle)  *)
(** The "pigeonhole principle" states a basic fact about counting:
   if you distribute more than [n] items into [n] pigeonholes, some 
   pigeonhole must contain at least two items.  As is often the case,
   this apparently trivial fact about numbers requires non-trivial
   machinery to prove, but we now have enough... *)

(** First a pair of useful lemmas (we already proved these for lists
    of naturals, but not for arbitrary lists). *)

Lemma app_length : forall (X:Type) (l1 l2 : list X),
  length (l1 ++ l2) = length l1 + length l2. 
Proof.
  intros X. induction l1 as [| l'].
  - intros. simpl. reflexivity.
  - intros. simpl. rewrite -> IHl1. reflexivity.
Qed.

Lemma appears_in_app_split : forall (X:Type) (x:X) (l:list X),
  appears_in x l -> 
  exists l1, exists l2, l = l1 ++ (x::l2).
Proof.
  intros. induction H as [| x0 x1 H'].
  - exists nil. simpl. exists l. reflexivity.
  - destruct IHH' as [Wit1 H0]. destruct H0 as [Wit2 H1]. exists (x0::Wit1). exists Wit2. simpl. rewrite <- H1. reflexivity.
Qed.

(** Now define a predicate [repeats] (analogous to [no_repeats] in the
   exercise above), such that [repeats X l] asserts that [l] contains
   at least one repeated element (of type [X]).  *)

Inductive repeats {X:Type} : list X -> Prop :=
  | rep_ap : forall (l: list X) (x: X), appears_in x l -> repeats (x::l)
  | rep_al : forall (l: list X) (x: X), repeats l -> repeats (x::l)
.

(** Now here's a way to formalize the pigeonhole principle. List [l2]
    represents a list of pigeonhole labels, and list [l1] represents
    the labels assigned to a list of items: if there are more items
    than labels, at least two items must have the same label.  This
    proof is much easier if you use the [excluded_middle] hypothesis
    to show that [appears_in] is decidable, i.e. [forall x
    l, (appears_in x l) \/ ~ (appears_in x l)].  However, it is also
    possible to make the proof go through _without_ assuming that
    [appears_in] is decidable; if you can manage to do this, you will
    not need the [excluded_middle] hypothesis. *)

Theorem pigeonhole_principle: forall (X:Type) (l1  l2:list X), 
   excluded_middle -> 
   (forall x, appears_in x l1 -> appears_in x l2) -> 
   length l2 < length l1 -> 
   repeats l1.  
Proof.
  intros X l1. induction l1 as [|x l1']. simpl. intros. inversion H1.
  intros. unfold excluded_middle in H. assert (appears_in x l1' \/ ~ (appears_in x l1')).
  apply H. inversion H2. apply rep_ap. apply H3.
  apply rep_al. destruct (appears_in_app_split X x l2 (H0 x (ai_here x l1'))) as [w1 [w2]]. 
  apply IHl1' with (l2:= w1++w2).
  - unfold excluded_middle. apply H.
  - intros. assert (H5 := H4). apply ai_later with (b:= x) in H4. apply H0 in H4. rewrite -> proof in H4. apply appears_in_app in H4. inversion H4.
    + apply app_appears_in. left. apply H6.
    + apply app_appears_in. right. inversion H6. 
      rewrite <- H8 in H3. apply H3 in H5. inversion H5. apply H8.
  - rewrite -> proof in H1. assert (forall (lst1 lst2: list X), length (lst1 ++ x :: lst2) = length (x :: lst1 ++ lst2)).
    intros. induction lst1 as [| lst1']. simpl. reflexivity. simpl. rewrite -> IHlst1. simpl. reflexivity.
    rewrite -> H4 with w1 w2 in H1. simpl in H1. unfold lt in H1. apply le_S_n in H1. unfold lt. apply H1.
Qed.

