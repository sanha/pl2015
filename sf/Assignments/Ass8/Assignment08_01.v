Require Export Assignment08_00.

(* problem #01: 10 points *)

(** **** Exercise: 2 stars (ceval_example2)  *)
Example ceval_example2:
    (X ::= ANum 0;; Y ::= ANum 1;; Z ::= ANum 2) / empty_state ||
    (update (update (update empty_state X 0) Y 1) Z 2).
Proof.
  apply E_Seq with (st' := update (empty_state) X 0). 
  - apply E_Ass. simpl. reflexivity.
  - apply E_Seq with (st' := update (update empty_state X 0) Y 1) ; try (apply E_Ass; simpl; reflexivity).
Qed.

(*-- Check --*)
Check ceval_example2 : 
    (X ::= ANum 0;; Y ::= ANum 1;; Z ::= ANum 2) / empty_state ||
    (update (update (update empty_state X 0) Y 1) Z 2).

