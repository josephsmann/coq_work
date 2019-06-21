Theorem forward_small : (forall A B : Prop,
A -> (A->B) -> B).
Proof.
 intros A.
 intros B.
 intros proof_of_A.
 intros A_implies_B.
 pose (proof_of_B := A_implies_B proof_of_A).
 exact proof_of_B.
Qed.

Theorem backward_large : 
(forall A B C : Prop, 
A -> (A->B) -> (B->C) -> C).
Proof.
 intros A B C.
 intros proof_of_A A_implies_B B_implies_C.
 refine (B_implies_C _).
   refine (A_implies_B _).
     exact proof_of_A.
Qed.

Theorem backward_huge : 
(forall A B C : Prop, 
A -> (A->B) -> (A->B->C) -> C).
Proof.
 intros A B C.
 intros proof_of_A A_implies_B A_imp_B_imp_C.
 refine (A_imp_B_imp_C _ _).
   exact proof_of_A.

   refine (A_implies_B _).
     exact proof_of_A.
Qed.

Theorem forward_huge : (forall A B C : Prop, A -> (A->B) -> (A->B->C) -> C).
Proof.
 intros A B C.
 intros proof_of_A A_implies_B A_imp_B_imp_C.
 pose (proof_of_B := A_implies_B proof_of_A).
 pose (proof_of_C := A_imp_B_imp_C proof_of_A proof_of_B).
 exact proof_of_C.
Show Proof.
Qed.

Theorem True_can_be_proven : True.
  exact I.
Qed.

Theorem False_cannot_be_proven : ~False.
Proof.
  unfold not.
  intros proof_of_False.
  exact proof_of_False.
Qed.


Theorem False_cannot_be_proven__again : ~False.
Proof.
  intros proof_of_False.
  case proof_of_False.
Qed.

Theorem thm_true_imp_false_a : ~(True -> False).
Proof.
  unfold not.
  intros T_implies_F.
  refine (T_implies_F _).
    exact I.
Show Proof.
Qed.

Theorem thm_true_imp_false : ~(True -> False).
Proof.
  intros T_implies_F.
  refine (T_implies_F _).
    exact I.
Qed.

Theorem absurd2 : forall A C : Prop, A -> ~ A -> C.
Proof.
  intros A C.
  intros proof_of_A proof_that_A_cannot_be_proven.
  unfold not in proof_that_A_cannot_be_proven.
  pose (proof_of_False := proof_that_A_cannot_be_proven proof_of_A).
  case proof_of_False.
Qed.


