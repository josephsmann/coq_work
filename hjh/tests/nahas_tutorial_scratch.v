Theorem backward_large : (forall A B C : Prop,
 A -> (A->B) -> (B->C) -> C).
Proof.
 intros A B C.
 intros proof_of_A A_implies_B B_implies_C.
 refine (B_implies_C _).
   refine (A_implies_B _).
     exact proof_of_A.
Qed.

Theorem backward_huge : (forall A B C : Prop, 
    A -> (A->B) -> (A->B->C) -> C).
Proof.
 intros A B C.
 intros proof_of_A A_implies_B A_imp_B_imp_C.
 refine (A_imp_B_imp_C _ _ ).
   exact proof_of_A.

   refine (A_implies_B _ ).
     exact proof_of_A.
Qed.

Theorem forward_huge : (forall A B C : Prop, 
    A -> (A->B) -> (A->B->C) -> C).
Proof.
 intros A B C.
 intros proof_of_A A_implies_B A_imp_B_imp_C.
 pose (proof_of_B := A_implies_B proof_of_A).
 pose (proof_of_C := A_imp_B_imp_C proof_of_A proof_of_B).
 exact proof_of_C.
Show Proof.
Qed.

Theorem X: True.
Proof.
  exact I.
Qed.

Print bool.

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

Theorem T1: forall A : Prop, A \/ ~A -> True.
Proof.
intros A.
intros H.
elim H.
  intros.
  exact I.

  intros.
  exact I.
Qed.

Theorem absurd2 : forall A C : Prop, 
  A -> ~ A -> C.
Proof.
  intros A C.
  intros proof_of_A proof_that_A_cannot_be_proven.
  unfold not in proof_that_A_cannot_be_proven.
  pose (proof_of_False := proof_that_A_cannot_be_proven proof_of_A).
  case proof_of_False.
  Show Proof.
Qed.
(* 
(fun (A C : Prop)
   (proof_of_A : A)
   (proof_that_A_cannot_be_proven : 
    ~ A) =>
 let proof_of_False :
   False :=
     proof_that_A_cannot_be_proven proof_of_A 
 in
 match
   proof_of_False
   return C
 with
 end)
*)



Require Import Bool.

Theorem true_is_True: Is_true true.
Proof.
  simpl.
  exact I.
Qed.

Theorem not_eqb_true_false: ~(Is_true (eqb true false)).
Proof.
  simpl.
  exact False_cannot_be_proven.
Qed.

Theorem eqb_a_a : (forall a : bool, Is_true (eqb a a)).
Proof.
  intros a.
  case a.
    (** suppose a is true *)
    simpl.
    exact I.

    (** suppose a is false *)
    simpl.
    exact I.
Qed.

Theorem thm_eqb_a_t: (forall a:bool, 
    (Is_true (eqb a true)) -> (Is_true a)).
Proof.
  intros a.
  case a.
    (** suppose a is true *)
    simpl.
    intros proof_of_True.
    exact I.

    (** suppose a is false *)
    simpl.
    intros proof_of_False.
    case proof_of_False.
Qed.


(* HJH case analysis *)

Theorem T2: forall A1 A2 C : Prop, 
(A1 -> C) /\ (A2 -> C) -> (A1 \/ A2 -> C).
Proof.
intros A1 A2 C.
intros Cases.
elim Cases.
intros Case1 Case2.
intros Select.
case Select.
exact Case1.
exact Case2.
Show Proof.
(*
(fun (A1 A2 C : Prop)
   (Cases : (A1 -> C) /\
            (A2 -> C)) =>
 and_ind
   (fun (Case1 : A1 -> C)
      (Case2 : A2 -> C)
      (Select : A1 \/ A2)
    =>
    match Select with
    | or_introl x =>
        Case1 x
    | or_intror x =>
        Case2 x
    end) Cases)
*)
Qed.

Check and_ind.

Theorem T2a: forall A1 A2 C : Prop, 
(A1 -> C) /\ (A2 -> C) -> (A1 \/ A2 -> C).
Proof.
intros.
case H0.
  elim H.

  intros.
  refine (H1 _).
  exact H3.

  elim H.
  intros.
  refine (H2 _).
  exact H3.

Show Proof.
(*
(fun (A1 A2 C : Prop)
   (H : (A1 -> C) /\
        (A2 -> C))
   (H0 : A1 \/ A2) =>
 match H0 with
 | or_introl x =>
     and_ind
       (fun
          (H1 : A1 -> C)
          (_ : A2 -> C)
          (H3 : A1) =>
        H1 H3) H x
 | or_intror x =>
     and_ind
       (fun (_ : A1 -> C)
          (H2 : A2 -> C)
          (H3 : A2) =>
        H2 H3) H x
 end)
*)
Qed.

Theorem T3: forall A B: Prop, A /\ B -> B.
Proof.
intros A B.
intros Conj.
destruct Conj as [L R].
Show Proof.
exact R.
Show Proof.
(*
(fun (A B : Prop) (Conj : A /\ B) =>
 match Conj with
 | conj _ R => R
 end)
*)
Qed.

Check and_ind.

Theorem T3a: forall A B: Prop, A /\ B -> B.
Proof.
intros A B.
Show Proof.
intros Conj.
elim Conj.
Show Proof.
intros.
Show Proof.
exact H0.
Show Proof.
(*
(fun (A B : Prop) (Conj : A /\ B) =>
 and_ind (fun (_ : A) (H0 : B) => H0) Conj)
*)

Qed.

Print and_ind.

(*
and_ind = 
fun (A B P : Prop) (f : A -> B -> P) (a : A /\ B) =>
match a with
| conj x x0 => f x x0
end
     : forall A B P : Prop, (A -> B -> P) -> A /\ B -> P

Arguments A, B, P are implicit
Argument scopes are [type_scope type_scope type_scope
  function_scope _]

*)







