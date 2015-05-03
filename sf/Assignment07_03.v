Require Export Assignment07_02.

(* problem #03: 20 points *)

(** **** Exercise: 3 stars  (bevalR)  *)
(** Write a relation [bevalR] in the same style as
    [aevalR], and prove that it is equivalent to [beval].*)

Inductive bevalR: bexp -> bool -> Prop :=
  | E_BT : BTrue || true
  | E_BF : BFalse || false
  | E_BEq_T : forall (a1 a2: aexp), beq_nat (aeval a1) (aeval a2) = true -> BEq a1 a2 || true
  | E_BEq_F : forall (a1 a2: aexp), beq_nat (aeval a1) (aeval a2) = false -> BEq a1 a2 || false
  | E_BLe_T : forall (a1 a2: aexp), ble_nat (aeval a1) (aeval a2) = true -> BLe a1 a2 || true
  | E_BLe_F : forall (a1 a2: aexp), ble_nat (aeval a1) (aeval a2) = false -> BLe a1 a2 || false
  | E_BNot : forall (be:bexp) (b: bool), be || b -> BNot be || negb b
  | E_BAnd : forall (be1 be2: bexp) (b1 b2: bool), be1 || b1 -> be2 || b2 
             -> BAnd be1 be2 || andb b1 b2

  where "e '||' n" := (bevalR e n) : type_scope.

Theorem beval_iff_bevalR : forall b bv,
  bevalR b bv <-> beval b = bv.
Proof.
  split.
  - intros. induction H ; simpl ; try subst; try reflexivity ; try auto.
  - intros. generalize dependent bv. induction b ; simpl ;
    try (intros; subst; constructor; auto) ;
    try (destruct bv ; constructor; auto).
Qed.
(** [] *)
