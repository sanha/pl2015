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
  | rep_l : forall (l: list X) (x: X), appears_in x l -> repeats (x::l)
  | rep_r : forall (l: list X) (x: X), appears_in x l -> repeats (l++x::[])
  | rep_ex_l: forall (l: list X) (x: X), repeats l -> repeats (x::l)
  | rep_ex_r: forall (l: list X) (x: X), repeats l -> repeats (l++x::[])
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
   intros X l1. induction l1 as [|x l1'].
  - simpl. intros. inversion H1.
  - 

  intros. unfold excluded_middle in H. assert (appears_in x l1' \/ ~ (appears_in x l1')). apply H. inversion H2.
    + apply rep_l. apply H3.
    + apply rep_ex_l. assert (exists lh: X, exists lt: list X, l2 = lh::lt).  


Qed.

