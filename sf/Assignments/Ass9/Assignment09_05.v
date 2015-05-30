Require Export Assignment09_04.

(* problem #05: 10 points *)

(** **** Exercise: 2 stars (if_minus_plus)  *)
(** Prove the following hoare triple using [hoare_if]: *)

Theorem if_minus_plus :
  {{fun st => True}}
  IFB (BLe (AId X) (AId Y))
    THEN (Z ::= AMinus (AId Y) (AId X))
    ELSE (Y ::= APlus (AId X) (AId Z))
  FI
  {{fun st => st Y = st X + st Z}}. 
Proof.
  eapply hoare_consequence_pre.
  apply hoare_if with (Q := fun st : state => st Y = st X + st Z) (b:= BLe (AId X) (AId Y)) 
                      (c1:= Z ::= AMinus (AId Y) (AId X)) (c2:= (Y ::= APlus (AId X) (AId Z))).
  - apply hoare_asgn.
  - apply hoare_asgn.
  - constructor.
    + intros. simpl in H0. unfold assn_sub. unfold update. simpl. apply le_plus_minus.
      apply ble_nat_true in H0. assumption.
    + intros. simpl in H0. unfold assn_sub. unfold update. reflexivity.
Qed.

(*-- Check --*)
Check if_minus_plus :
  {{fun st => True}}
  IFB (BLe (AId X) (AId Y))
    THEN (Z ::= AMinus (AId Y) (AId X))
    ELSE (Y ::= APlus (AId X) (AId Z))
  FI
  {{fun st => st Y = st X + st Z}}. 

